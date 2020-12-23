%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 (4096 expanded)
%              Number of clauses        :   83 (1393 expanded)
%              Number of leaves         :   13 (1016 expanded)
%              Depth                    :   17
%              Number of atoms          :  636 (41249 expanded)
%              Number of equality atoms :   71 ( 985 expanded)
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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
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
      & ( m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( esk2_3(X17,X18,X19) = u1_struct_0(X18)
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( X19 != k6_tmap_1(X17,esk2_3(X17,X18,X19))
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_15,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_16,plain,(
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

fof(c_0_17,plain,(
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

fof(c_0_18,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

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

cnf(c_0_23,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
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
      & ( m1_subset_1(esk3_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))
        | X24 = k9_tmap_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( esk3_3(X22,X23,X24) = u1_struct_0(X23)
        | X24 = k9_tmap_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk3_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk3_3(X22,X23,X24)))
        | X24 = k9_tmap_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))))
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
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

cnf(c_0_33,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_36,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_tsep_1(X28,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | X29 != u1_struct_0(X28)
        | v3_pre_topc(X29,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk4_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))
        | v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( esk4_2(X27,X28) = u1_struct_0(X28)
        | v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(esk4_2(X27,X28),X27)
        | v1_tsep_1(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_39,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_45,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_47,plain,(
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

cnf(c_0_48,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_50,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_51,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,X1)),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,X1))
    | X1 != u1_struct_0(esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_27]),c_0_43]),c_0_44]),c_0_26]),c_0_28])]),c_0_29])).

cnf(c_0_53,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(X1)) = k8_tmap_1(esk5_0,esk6_0)
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | m1_subset_1(esk4_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_28])])).

cnf(c_0_55,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_26]),c_0_49]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_26]),c_0_49]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_60,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk5_0,esk6_0)) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_53]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k6_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0))
    | v1_tsep_1(esk6_0,esk5_0)
    | esk4_2(esk5_0,esk6_0) != u1_struct_0(X2)
    | X1 != k8_tmap_1(esk5_0,X2)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_54]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( esk4_2(esk5_0,esk6_0) = u1_struct_0(esk6_0)
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_26]),c_0_28])])).

fof(c_0_64,plain,(
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

fof(c_0_65,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_66,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k7_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X1,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59])])).

cnf(c_0_68,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( X1 = k6_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | v1_tsep_1(esk6_0,esk5_0)
    | u1_struct_0(esk6_0) != u1_struct_0(X2)
    | X1 != k8_tmap_1(esk5_0,X2)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70]),c_0_44])])).

cnf(c_0_76,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( k8_tmap_1(esk5_0,X1) = k6_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | v1_tsep_1(esk6_0,esk5_0)
    | u1_struct_0(esk6_0) != u1_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(esk5_0,X1))
    | ~ v2_pre_topc(k8_tmap_1(esk5_0,X1))
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_pre_topc(k8_tmap_1(esk5_0,X1)) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_79,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_pre_topc(esk6_0,esk5_0)
    | ~ v1_funct_1(k9_tmap_1(esk5_0,esk6_0))
    | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))
    | ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_82,plain,
    ( v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_20])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_20]),c_0_26]),c_0_28])])).

cnf(c_0_85,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0)
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_26]),c_0_80])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0)
    | ~ m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))
    | ~ v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_26])]),c_0_44])])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(X1)),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ v3_pre_topc(u1_struct_0(X1),esk5_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_53]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_89,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_28])]),c_0_29])).

cnf(c_0_90,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0)
    | v3_pre_topc(u1_struct_0(X1),esk5_0)
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_26]),c_0_28])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v1_tsep_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_43])]),c_0_42])])).

cnf(c_0_93,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_26])])).

cnf(c_0_94,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_63]),c_0_26]),c_0_28])])).

cnf(c_0_95,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_63]),c_0_26]),c_0_28])])).

cnf(c_0_96,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,X2))
    | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | ~ v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
    | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_97,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0)
    | v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_26])).

cnf(c_0_98,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk6_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk5_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | u1_struct_0(X1) != u1_struct_0(esk6_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_95]),c_0_26]),c_0_28])])).

cnf(c_0_100,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_96,c_0_40]),c_0_39]),c_0_37])).

cnf(c_0_101,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk6_0),esk5_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_26])).

cnf(c_0_103,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_89]),c_0_27]),c_0_28])]),c_0_98]),c_0_29])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_102,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))
    | v1_tsep_1(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_106,negated_conjecture,
    ( ~ v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( u1_struct_0(esk6_0) != u1_struct_0(X1)
    | ~ v1_tsep_1(X1,esk5_0)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_104]),c_0_28])]),c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( v1_tsep_1(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.51  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.042 s
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(t122_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_tmap_1)).
% 0.19/0.51  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.19/0.51  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.51  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.19/0.51  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.19/0.51  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.19/0.51  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.19/0.51  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.19/0.51  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 0.19/0.51  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.19/0.51  fof(t113_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.19/0.51  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.51  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.51  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k9_tmap_1(X1,X2),X1,k8_tmap_1(X1,X2)))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t122_tmap_1])).
% 0.19/0.51  fof(c_0_14, plain, ![X17, X18, X19, X20]:((X19!=k8_tmap_1(X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(X20!=u1_struct_0(X18)|X19=k6_tmap_1(X17,X20)))|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((m1_subset_1(esk2_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((esk2_3(X17,X18,X19)=u1_struct_0(X18)|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(X19!=k6_tmap_1(X17,esk2_3(X17,X18,X19))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.19/0.51  fof(c_0_15, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_pre_topc(X42,X41)|m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.51  fof(c_0_16, plain, ![X37, X38]:((u1_struct_0(k6_tmap_1(X37,X38))=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(u1_pre_topc(k6_tmap_1(X37,X38))=k5_tmap_1(X37,X38)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.19/0.51  fof(c_0_17, plain, ![X35, X36]:(((v1_funct_1(k9_tmap_1(X35,X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))&(v1_funct_2(k9_tmap_1(X35,X36),u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35))))&(m1_subset_1(k9_tmap_1(X35,X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.19/0.51  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_pre_topc(esk6_0,esk5_0)&((~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|(~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))))&(((((v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0))&(v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|v1_tsep_1(esk6_0,esk5_0)))&(v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)))&(m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|v1_tsep_1(esk6_0,esk5_0)))&((((v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|m1_pre_topc(esk6_0,esk5_0))&(v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|m1_pre_topc(esk6_0,esk5_0)))&(v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|m1_pre_topc(esk6_0,esk5_0)))&(m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|m1_pre_topc(esk6_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 0.19/0.51  cnf(c_0_19, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.51  fof(c_0_21, plain, ![X33, X34]:(((v1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))&(v2_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33))))&(l1_pre_topc(k8_tmap_1(X33,X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_pre_topc(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.19/0.51  fof(c_0_22, plain, ![X31, X32]:(((v1_funct_1(k7_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))&(v1_funct_2(k7_tmap_1(X31,X32),u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31))))))&(m1_subset_1(k7_tmap_1(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(k6_tmap_1(X31,X32)))))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.19/0.51  cnf(c_0_23, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.51  fof(c_0_24, plain, ![X22, X23, X24, X25]:((X24!=k9_tmap_1(X22,X23)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|(X25!=u1_struct_0(X23)|r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X25)),X24,k7_tmap_1(X22,X25))))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((m1_subset_1(esk3_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((esk3_3(X22,X23,X24)=u1_struct_0(X23)|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_funct_2(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,esk3_3(X22,X23,X24))),X24,k7_tmap_1(X22,esk3_3(X22,X23,X24)))|X24=k9_tmap_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23)))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k8_tmap_1(X22,X23))))))|~m1_pre_topc(X23,X22)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.19/0.51  cnf(c_0_25, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  cnf(c_0_30, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_31, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.51  cnf(c_0_32, plain, (X1=k6_tmap_1(X2,u1_struct_0(X3))|v2_struct_0(X2)|u1_struct_0(X3)!=u1_struct_0(X4)|X1!=k8_tmap_1(X2,X4)|~v1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.51  cnf(c_0_33, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.51  cnf(c_0_34, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.51  cnf(c_0_35, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.51  fof(c_0_36, plain, ![X27, X28, X29]:((~v1_tsep_1(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(X29!=u1_struct_0(X28)|v3_pre_topc(X29,X27)))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((m1_subset_1(esk4_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((esk4_2(X27,X28)=u1_struct_0(X28)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(~v3_pre_topc(esk4_2(X27,X28),X27)|v1_tsep_1(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 0.19/0.51  cnf(c_0_37, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_38, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.19/0.51  cnf(c_0_39, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_40, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_41, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.51  cnf(c_0_42, negated_conjecture, (m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_43, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_44, negated_conjecture, (v1_funct_1(k9_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_45, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,u1_struct_0(X3))|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.51  cnf(c_0_46, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  fof(c_0_47, plain, ![X11, X12, X13, X14, X15, X16]:((~r1_funct_2(X11,X12,X13,X14,X15,X16)|X15=X16|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(X15!=X16|r1_funct_2(X11,X12,X13,X14,X15,X16)|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.19/0.51  cnf(c_0_48, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_20])).
% 0.19/0.51  cnf(c_0_49, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_50, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_20])).
% 0.19/0.51  cnf(c_0_51, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.19/0.51  cnf(c_0_52, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,X1)),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,X1))|X1!=u1_struct_0(esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_27]), c_0_43]), c_0_44]), c_0_26]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_53, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(X1))=k8_tmap_1(esk5_0,esk6_0)|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_54, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|m1_subset_1(esk4_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_26]), c_0_28])])).
% 0.19/0.51  cnf(c_0_55, plain, (esk4_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_56, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.51  cnf(c_0_57, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_26]), c_0_49]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_58, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_26]), c_0_49]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_59, negated_conjecture, (v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_60, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_52, c_0_49])).
% 0.19/0.51  cnf(c_0_61, negated_conjecture, (u1_struct_0(k8_tmap_1(esk5_0,esk6_0))=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_53]), c_0_26])])).
% 0.19/0.51  cnf(c_0_62, negated_conjecture, (X1=k6_tmap_1(esk5_0,esk4_2(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)|esk4_2(esk5_0,esk6_0)!=u1_struct_0(X2)|X1!=k8_tmap_1(esk5_0,X2)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk5_0)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_54]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_63, negated_conjecture, (esk4_2(esk5_0,esk6_0)=u1_struct_0(esk6_0)|v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_26]), c_0_28])])).
% 0.19/0.51  fof(c_0_64, plain, ![X39, X40]:(((((v1_funct_1(k7_tmap_1(X39,X40))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))|~v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(~v1_funct_1(k7_tmap_1(X39,X40))|~v1_funct_2(k7_tmap_1(X39,X40),u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))|~v5_pre_topc(k7_tmap_1(X39,X40),X39,k6_tmap_1(X39,X40))|~m1_subset_1(k7_tmap_1(X39,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(k6_tmap_1(X39,X40)))))|v3_pre_topc(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t113_tmap_1])])])])])).
% 0.19/0.51  fof(c_0_65, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.51  fof(c_0_66, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.51  cnf(c_0_67, negated_conjecture, (X1=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X1,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59])])).
% 0.19/0.51  cnf(c_0_68, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.51  cnf(c_0_69, negated_conjecture, (m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(rw,[status(thm)],[c_0_42, c_0_61])).
% 0.19/0.51  cnf(c_0_70, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_43, c_0_61])).
% 0.19/0.51  cnf(c_0_71, negated_conjecture, (X1=k6_tmap_1(esk5_0,u1_struct_0(esk6_0))|v1_tsep_1(esk6_0,esk5_0)|u1_struct_0(esk6_0)!=u1_struct_0(X2)|X1!=k8_tmap_1(esk5_0,X2)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk5_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.51  cnf(c_0_72, plain, (v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.51  cnf(c_0_73, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.51  cnf(c_0_74, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.51  cnf(c_0_75, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70]), c_0_44])])).
% 0.19/0.51  cnf(c_0_76, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_77, negated_conjecture, (k8_tmap_1(esk5_0,X1)=k6_tmap_1(esk5_0,u1_struct_0(esk6_0))|v1_tsep_1(esk6_0,esk5_0)|u1_struct_0(esk6_0)!=u1_struct_0(X1)|~v1_pre_topc(k8_tmap_1(esk5_0,X1))|~v2_pre_topc(k8_tmap_1(esk5_0,X1))|~m1_pre_topc(X1,esk5_0)|~l1_pre_topc(k8_tmap_1(esk5_0,X1))), inference(er,[status(thm)],[c_0_71])).
% 0.19/0.51  cnf(c_0_78, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_79, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_80, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_81, negated_conjecture, (~v1_tsep_1(esk6_0,esk5_0)|~m1_pre_topc(esk6_0,esk5_0)|~v1_funct_1(k9_tmap_1(esk5_0,esk6_0))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))|~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  cnf(c_0_82, plain, (v5_pre_topc(k7_tmap_1(X1,u1_struct_0(X2)),X1,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_72, c_0_20])).
% 0.19/0.51  cnf(c_0_83, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.51  cnf(c_0_84, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_20]), c_0_26]), c_0_28])])).
% 0.19/0.51  cnf(c_0_85, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_76, c_0_20])).
% 0.19/0.51  cnf(c_0_86, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)|v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_26]), c_0_80])])).
% 0.19/0.51  cnf(c_0_87, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)|~m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))))|~v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_26])]), c_0_44])])).
% 0.19/0.51  cnf(c_0_88, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk5_0,u1_struct_0(X1)),esk5_0,k8_tmap_1(esk5_0,esk6_0))|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~v3_pre_topc(u1_struct_0(X1),esk5_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_53]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_89, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_28])]), c_0_29])).
% 0.19/0.51  cnf(c_0_90, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk4_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.51  cnf(c_0_91, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)|v3_pre_topc(u1_struct_0(X1),esk5_0)|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_26]), c_0_28])])).
% 0.19/0.51  cnf(c_0_92, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v1_tsep_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_43])]), c_0_42])])).
% 0.19/0.51  cnf(c_0_93, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_26])])).
% 0.19/0.51  cnf(c_0_94, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_63]), c_0_26]), c_0_28])])).
% 0.19/0.51  cnf(c_0_95, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_63]), c_0_26]), c_0_28])])).
% 0.19/0.51  cnf(c_0_96, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|~v1_funct_1(k7_tmap_1(X1,X2))|~v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|~v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))|~m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.51  cnf(c_0_97, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)|v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_91, c_0_26])).
% 0.19/0.51  cnf(c_0_98, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk6_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.19/0.51  cnf(c_0_99, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk5_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|u1_struct_0(X1)!=u1_struct_0(esk6_0)|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_95]), c_0_26]), c_0_28])])).
% 0.19/0.51  cnf(c_0_100, plain, (v3_pre_topc(X1,X2)|v2_struct_0(X2)|~v5_pre_topc(k7_tmap_1(X2,X1),X2,k6_tmap_1(X2,X1))|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_96, c_0_40]), c_0_39]), c_0_37])).
% 0.19/0.51  cnf(c_0_101, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)), inference(sr,[status(thm)],[c_0_97, c_0_98])).
% 0.19/0.51  cnf(c_0_102, negated_conjecture, (v3_pre_topc(u1_struct_0(esk6_0),esk5_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_99, c_0_26])).
% 0.19/0.51  cnf(c_0_103, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_89]), c_0_27]), c_0_28])]), c_0_98]), c_0_29])).
% 0.19/0.51  cnf(c_0_104, negated_conjecture, (m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[c_0_102, c_0_98])).
% 0.19/0.51  cnf(c_0_105, negated_conjecture, (v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))|v1_tsep_1(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.51  cnf(c_0_106, negated_conjecture, (~v5_pre_topc(k9_tmap_1(esk5_0,esk6_0),esk5_0,k8_tmap_1(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.19/0.51  cnf(c_0_107, negated_conjecture, (u1_struct_0(esk6_0)!=u1_struct_0(X1)|~v1_tsep_1(X1,esk5_0)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_104]), c_0_28])]), c_0_98])).
% 0.19/0.51  cnf(c_0_108, negated_conjecture, (v1_tsep_1(esk6_0,esk5_0)), inference(sr,[status(thm)],[c_0_105, c_0_106])).
% 0.19/0.51  cnf(c_0_109, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_26])]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 110
% 0.19/0.51  # Proof object clause steps            : 83
% 0.19/0.51  # Proof object formula steps           : 27
% 0.19/0.51  # Proof object conjectures             : 54
% 0.19/0.51  # Proof object clause conjectures      : 51
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 28
% 0.19/0.51  # Proof object initial formulas used   : 13
% 0.19/0.51  # Proof object generating inferences   : 45
% 0.19/0.51  # Proof object simplifying inferences  : 132
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 14
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 47
% 0.19/0.51  # Removed in clause preprocessing      : 0
% 0.19/0.51  # Initial clauses in saturation        : 47
% 0.19/0.51  # Processed clauses                    : 710
% 0.19/0.51  # ...of these trivial                  : 42
% 0.19/0.51  # ...subsumed                          : 151
% 0.19/0.51  # ...remaining for further processing  : 517
% 0.19/0.51  # Other redundant clauses eliminated   : 1
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 22
% 0.19/0.51  # Backward-rewritten                   : 195
% 0.19/0.51  # Generated clauses                    : 2060
% 0.19/0.51  # ...of the previous two non-trivial   : 2024
% 0.19/0.52  # Contextual simplify-reflections      : 48
% 0.19/0.52  # Paramodulations                      : 2034
% 0.19/0.52  # Factorizations                       : 10
% 0.19/0.52  # Equation resolutions                 : 13
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 296
% 0.19/0.52  #    Positive orientable unit clauses  : 36
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 3
% 0.19/0.52  #    Non-unit-clauses                  : 257
% 0.19/0.52  # Current number of unprocessed clauses: 1304
% 0.19/0.52  # ...number of literals in the above   : 7078
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 220
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 39855
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 3864
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 210
% 0.19/0.52  # Unit Clause-clause subsumption calls : 1005
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 40
% 0.19/0.52  # BW rewrite match successes           : 15
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 96230
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.164 s
% 0.19/0.52  # System time              : 0.010 s
% 0.19/0.52  # Total time               : 0.174 s
% 0.19/0.52  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
