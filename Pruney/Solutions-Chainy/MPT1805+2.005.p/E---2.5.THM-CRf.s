%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 (24249 expanded)
%              Number of clauses        :   76 (8192 expanded)
%              Number of leaves         :   12 (6224 expanded)
%              Depth                    :   18
%              Number of atoms          :  561 (175628 expanded)
%              Number of equality atoms :   64 (8268 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t121_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
            & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
            & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
            & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_tmap_1)).

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

fof(t112_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_tmap_1)).

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

fof(c_0_12,plain,(
    ! [X31,X32] :
      ( ( u1_struct_0(k6_tmap_1(X31,X32)) = u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( u1_pre_topc(k6_tmap_1(X31,X32)) = k5_tmap_1(X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_13,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | m1_subset_1(u1_struct_0(X37),k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
              & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
              & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
              & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t121_tmap_1])).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X17 != k8_tmap_1(X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | X18 != u1_struct_0(X16)
        | X17 = k6_tmap_1(X15,X18)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( esk1_3(X15,X16,X17) = u1_struct_0(X16)
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( X17 != k6_tmap_1(X15,esk1_3(X15,X16,X17))
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_16,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( v2_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( l1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_17,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))
      | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
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

cnf(c_0_21,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])]),c_0_21]),c_0_18]),c_0_22]),c_0_23])).

fof(c_0_30,plain,(
    ! [X25,X26] :
      ( ( v1_funct_1(k7_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( v1_funct_2(k7_tmap_1(X25,X26),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( m1_subset_1(k7_tmap_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_31,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X22 != k9_tmap_1(X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | X23 != u1_struct_0(X21)
        | r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,X23)),X22,k7_tmap_1(X20,X23))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))
        | X22 = k9_tmap_1(X20,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( esk2_3(X20,X21,X22) = u1_struct_0(X21)
        | X22 = k9_tmap_1(X20,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,esk2_3(X20,X21,X22))),X22,k7_tmap_1(X20,esk2_3(X20,X21,X22)))
        | X22 = k9_tmap_1(X20,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_34,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_39,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_36]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,X1) = u1_struct_0(esk4_0)
    | X1 = k9_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

fof(c_0_46,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35))
        | u1_struct_0(X35) != X34
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v1_funct_2(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35),u1_struct_0(X35),u1_struct_0(k6_tmap_1(X33,X34)))
        | u1_struct_0(X35) != X34
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v5_pre_topc(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35),X35,k6_tmap_1(X33,X34))
        | u1_struct_0(X35) != X34
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k6_tmap_1(X33,X34)))))
        | u1_struct_0(X35) != X34
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t112_tmap_1])])])])])).

cnf(c_0_47,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_43])]),c_0_44])).

cnf(c_0_49,plain,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_18]),c_0_25]),c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_18]),c_0_25]),c_0_27])])).

cnf(c_0_52,plain,
    ( v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,plain,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,plain,
    ( v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_18])).

cnf(c_0_60,plain,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_18])).

cnf(c_0_61,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2),X2,k6_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_36]),c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_33]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_57]),c_0_33]),c_0_33]),c_0_36]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_57]),c_0_33]),c_0_33]),c_0_36]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_57]),c_0_33]),c_0_33]),c_0_25]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

fof(c_0_67,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(k9_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X29) )
      & ( v1_funct_2(k9_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X29) )
      & ( m1_subset_1(k9_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_pre_topc(X30,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_68,plain,(
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

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_70,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_71,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_69])])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_69])])).

cnf(c_0_77,plain,
    ( r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])]),c_0_71]),c_0_72]),c_0_18]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

fof(c_0_80,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_43])])).

cnf(c_0_82,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_25]),c_0_36]),c_0_33]),c_0_36]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_84]),c_0_85])])).

fof(c_0_88,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_89,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_28])).

cnf(c_0_90,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_25]),c_0_33]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_92,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_27])])).

cnf(c_0_93,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_25]),c_0_33]),c_0_33]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_33]),c_0_33]),c_0_36]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_25]),c_0_33]),c_0_33]),c_0_36]),c_0_26]),c_0_27])]),c_0_28]),c_0_58])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_94,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_96])]),c_0_97]),c_0_98]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:37:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.19/0.40  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.19/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.40  fof(t121_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(((v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))&v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2)))&m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_tmap_1)).
% 0.19/0.40  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.19/0.40  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.19/0.40  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.19/0.40  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.19/0.40  fof(t112_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(u1_struct_0(X3)=X2=>(((v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))&v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2)))&m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_tmap_1)).
% 0.19/0.40  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.19/0.40  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.19/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.40  fof(c_0_12, plain, ![X31, X32]:((u1_struct_0(k6_tmap_1(X31,X32))=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(u1_pre_topc(k6_tmap_1(X31,X32))=k5_tmap_1(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.19/0.40  fof(c_0_13, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|m1_subset_1(u1_struct_0(X37),k1_zfmisc_1(u1_struct_0(X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(((v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))&v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))&v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2)))&m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))))))), inference(assume_negation,[status(cth)],[t121_tmap_1])).
% 0.19/0.40  fof(c_0_15, plain, ![X15, X16, X17, X18]:((X17!=k8_tmap_1(X15,X16)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))|(X18!=u1_struct_0(X16)|X17=k6_tmap_1(X15,X18)))|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((esk1_3(X15,X16,X17)=u1_struct_0(X16)|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(X17!=k6_tmap_1(X15,esk1_3(X15,X16,X17))|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.19/0.40  fof(c_0_16, plain, ![X27, X28]:(((v1_pre_topc(k8_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_pre_topc(X28,X27)))&(v2_pre_topc(k8_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_pre_topc(X28,X27))))&(l1_pre_topc(k8_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_pre_topc(X28,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.19/0.40  cnf(c_0_17, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_18, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(~v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))|~v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.40  cnf(c_0_20, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_21, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_22, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_23, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_24, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_29, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])]), c_0_21]), c_0_18]), c_0_22]), c_0_23])).
% 0.19/0.40  fof(c_0_30, plain, ![X25, X26]:(((v1_funct_1(k7_tmap_1(X25,X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&(v1_funct_2(k7_tmap_1(X25,X26),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))))))&(m1_subset_1(k7_tmap_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.19/0.40  fof(c_0_31, plain, ![X20, X21, X22, X23]:((X22!=k9_tmap_1(X20,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(X23!=u1_struct_0(X21)|r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,X23)),X22,k7_tmap_1(X20,X23))))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((m1_subset_1(esk2_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))|X22=k9_tmap_1(X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((esk2_3(X20,X21,X22)=u1_struct_0(X21)|X22=k9_tmap_1(X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,esk2_3(X20,X21,X22))),X22,k7_tmap_1(X20,esk2_3(X20,X21,X22)))|X22=k9_tmap_1(X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))=k8_tmap_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_34, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_35, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (u1_struct_0(k8_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.40  cnf(c_0_37, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_38, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_18])).
% 0.19/0.40  cnf(c_0_39, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.40  cnf(c_0_40, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (X1=k9_tmap_1(esk3_0,esk4_0)|m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_36]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (esk2_3(esk3_0,esk4_0,X1)=u1_struct_0(esk4_0)|X1=k9_tmap_1(esk3_0,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  fof(c_0_46, plain, ![X33, X34, X35]:((((v1_funct_1(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35))|u1_struct_0(X35)!=X34|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(v1_funct_2(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35),u1_struct_0(X35),u1_struct_0(k6_tmap_1(X33,X34)))|u1_struct_0(X35)!=X34|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(v5_pre_topc(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35),X35,k6_tmap_1(X33,X34))|u1_struct_0(X35)!=X34|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(m1_subset_1(k2_tmap_1(X33,k6_tmap_1(X33,X34),k7_tmap_1(X33,X34),X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(k6_tmap_1(X33,X34)))))|u1_struct_0(X35)!=X34|(v2_struct_0(X35)|~m1_pre_topc(X35,X33))|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t112_tmap_1])])])])])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])]), c_0_44])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)|k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_42]), c_0_43])]), c_0_44])).
% 0.19/0.40  cnf(c_0_49, plain, (v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_18]), c_0_25]), c_0_27])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)|k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_18]), c_0_25]), c_0_27])])).
% 0.19/0.40  cnf(c_0_52, plain, (v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_53, plain, (m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_54, plain, (v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (~v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))|~v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_56, plain, (v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_18])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_59, plain, (v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_18])).
% 0.19/0.40  cnf(c_0_60, plain, (m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_18])).
% 0.19/0.40  cnf(c_0_61, plain, (v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),X2),X2,k6_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_18])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_36]), c_0_36])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_33]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_57]), c_0_33]), c_0_33]), c_0_36]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_57]), c_0_33]), c_0_33]), c_0_36]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))|m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_57]), c_0_33]), c_0_33]), c_0_25]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  fof(c_0_67, plain, ![X29, X30]:(((v1_funct_1(k9_tmap_1(X29,X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_pre_topc(X30,X29)))&(v1_funct_2(k9_tmap_1(X29,X30),u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_pre_topc(X30,X29))))&(m1_subset_1(k9_tmap_1(X29,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(k8_tmap_1(X29,X30)))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_pre_topc(X30,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.19/0.40  fof(c_0_68, plain, ![X9, X10, X11, X12, X13, X14]:((~r1_funct_2(X9,X10,X11,X12,X13,X14)|X13=X14|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(X13!=X14|r1_funct_2(X9,X10,X11,X12,X13,X14)|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66])).
% 0.19/0.40  cnf(c_0_70, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_71, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_72, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_73, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.40  cnf(c_0_74, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_69])])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_69])])).
% 0.19/0.40  cnf(c_0_77, plain, (r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])]), c_0_71]), c_0_72]), c_0_18]), c_0_73])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  fof(c_0_80, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (X1=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_43])])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_25]), c_0_36]), c_0_33]), c_0_36]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_78, c_0_36])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_79, c_0_36])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (v1_funct_1(k9_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.19/0.40  cnf(c_0_86, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_84]), c_0_85])])).
% 0.19/0.40  fof(c_0_88, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.40  cnf(c_0_89, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_28])).
% 0.19/0.40  cnf(c_0_90, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_25]), c_0_33]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k9_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_27])])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_25]), c_0_33]), c_0_33]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_25]), c_0_33]), c_0_33]), c_0_36]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_95, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_25]), c_0_33]), c_0_33]), c_0_36]), c_0_26]), c_0_27])]), c_0_28]), c_0_58])).
% 0.19/0.40  cnf(c_0_96, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_93, c_0_92])).
% 0.19/0.40  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_94, c_0_92])).
% 0.19/0.40  cnf(c_0_99, negated_conjecture, (v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_95, c_0_92])).
% 0.19/0.40  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_96])]), c_0_97]), c_0_98]), c_0_99])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 101
% 0.19/0.40  # Proof object clause steps            : 76
% 0.19/0.40  # Proof object formula steps           : 25
% 0.19/0.40  # Proof object conjectures             : 49
% 0.19/0.40  # Proof object clause conjectures      : 46
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 28
% 0.19/0.40  # Proof object initial formulas used   : 12
% 0.19/0.40  # Proof object generating inferences   : 31
% 0.19/0.40  # Proof object simplifying inferences  : 176
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 12
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 34
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 34
% 0.19/0.40  # Processed clauses                    : 278
% 0.19/0.40  # ...of these trivial                  : 21
% 0.19/0.40  # ...subsumed                          : 49
% 0.19/0.40  # ...remaining for further processing  : 207
% 0.19/0.40  # Other redundant clauses eliminated   : 9
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 6
% 0.19/0.40  # Backward-rewritten                   : 51
% 0.19/0.40  # Generated clauses                    : 405
% 0.19/0.40  # ...of the previous two non-trivial   : 390
% 0.19/0.40  # Contextual simplify-reflections      : 22
% 0.19/0.40  # Paramodulations                      : 392
% 0.19/0.40  # Factorizations                       : 6
% 0.19/0.40  # Equation resolutions                 : 9
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 109
% 0.19/0.40  #    Positive orientable unit clauses  : 19
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 88
% 0.19/0.40  # Current number of unprocessed clauses: 171
% 0.19/0.40  # ...number of literals in the above   : 1084
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 91
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 4619
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 726
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 76
% 0.19/0.40  # Unit Clause-clause subsumption calls : 528
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 10
% 0.19/0.40  # BW rewrite match successes           : 6
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 22801
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.057 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.063 s
% 0.19/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
