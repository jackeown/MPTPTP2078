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
% DateTime   : Thu Dec  3 11:18:22 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 384 expanded)
%              Number of clauses        :   50 ( 138 expanded)
%              Number of leaves         :   13 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  389 (2604 expanded)
%              Number of equality atoms :   67 ( 396 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

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

fof(fc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

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

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

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

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17] :
      ( ( X14 = X16
        | g1_pre_topc(X14,X15) != g1_pre_topc(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) )
      & ( X15 = X17
        | g1_pre_topc(X14,X15) != g1_pre_topc(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_15,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ( ~ v1_tsep_1(esk4_0,esk3_0)
      | ~ m1_pre_topc(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) )
    & ( v1_tsep_1(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) )
    & ( m1_pre_topc(esk4_0,esk3_0)
      | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X13] :
      ( ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) )
      & ( v1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).

fof(c_0_25,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X22 != k8_tmap_1(X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | X23 != u1_struct_0(X21)
        | X22 = k6_tmap_1(X20,X23)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))
        | X22 = k8_tmap_1(X20,X21)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( esk1_3(X20,X21,X22) = u1_struct_0(X21)
        | X22 = k8_tmap_1(X20,X21)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( X22 != k6_tmap_1(X20,esk1_3(X20,X21,X22))
        | X22 = k8_tmap_1(X20,X21)
        | ~ v1_pre_topc(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_26,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_27,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_29,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | ~ v1_pre_topc(X7)
      | X7 = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
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

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_38,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_tsep_1(X26,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | X27 != u1_struct_0(X26)
        | v3_pre_topc(X27,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk2_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v1_tsep_1(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( esk2_2(X25,X26) = u1_struct_0(X26)
        | v1_tsep_1(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v3_pre_topc(esk2_2(X25,X26),X25)
        | v1_tsep_1(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

fof(c_0_39,plain,(
    ! [X8,X9] :
      ( ( ~ v3_pre_topc(X9,X8)
        | r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(X9,u1_pre_topc(X8))
        | v3_pre_topc(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

fof(c_0_40,plain,(
    ! [X35,X36] :
      ( ( ~ r2_hidden(X36,u1_pre_topc(X35))
        | u1_pre_topc(X35) = k5_tmap_1(X35,X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( u1_pre_topc(X35) != k5_tmap_1(X35,X36)
        | r2_hidden(X36,u1_pre_topc(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_41,negated_conjecture,
    ( u1_pre_topc(esk3_0) = X1
    | v1_tsep_1(esk4_0,esk3_0)
    | k8_tmap_1(esk3_0,esk4_0) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])])).

cnf(c_0_42,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_23])]),c_0_20])).

cnf(c_0_45,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])]),c_0_35]),c_0_21]),c_0_36]),c_0_37])).

fof(c_0_47,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | k6_tmap_1(X29,X30) = g1_pre_topc(u1_struct_0(X29),k5_tmap_1(X29,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_48,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) = u1_pre_topc(esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42])]),c_0_43])]),c_0_44])).

cnf(c_0_53,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ r2_hidden(esk2_2(X2,X1),u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_58,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))
    | k5_tmap_1(X1,u1_struct_0(X2)) != u1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( k5_tmap_1(esk3_0,u1_struct_0(esk4_0)) = u1_pre_topc(esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_22]),c_0_31]),c_0_23])]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_31])])).

cnf(c_0_62,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22]),c_0_31]),c_0_23])]),c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( k6_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_31]),c_0_23])])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_68,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( k6_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_35])).

cnf(c_0_71,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_35])).

cnf(c_0_72,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_23])])).

cnf(c_0_73,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_23])])).

cnf(c_0_75,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_66]),c_0_31])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_46]),c_0_22]),c_0_31]),c_0_23])]),c_0_20]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.51/2.69  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 2.51/2.69  # and selection function PSelectUnlessUniqMaxPos.
% 2.51/2.69  #
% 2.51/2.69  # Preprocessing time       : 0.032 s
% 2.51/2.69  # Presaturation interreduction done
% 2.51/2.69  
% 2.51/2.69  # Proof found!
% 2.51/2.69  # SZS status Theorem
% 2.51/2.69  # SZS output start CNFRefutation
% 2.51/2.69  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 2.51/2.69  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.51/2.69  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.51/2.69  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 2.51/2.69  fof(fc7_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>(~(v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))&v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 2.51/2.69  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 2.51/2.69  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.51/2.69  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.51/2.69  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.51/2.69  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 2.51/2.69  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.51/2.69  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 2.51/2.69  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.51/2.69  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 2.51/2.69  fof(c_0_14, plain, ![X14, X15, X16, X17]:((X14=X16|g1_pre_topc(X14,X15)!=g1_pre_topc(X16,X17)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))&(X15=X17|g1_pre_topc(X14,X15)!=g1_pre_topc(X16,X17)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 2.51/2.69  fof(c_0_15, plain, ![X12]:(~l1_pre_topc(X12)|m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 2.51/2.69  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0))&((v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0))&(m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 2.51/2.69  fof(c_0_17, plain, ![X31, X32]:(((v1_pre_topc(k8_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_pre_topc(X32,X31)))&(v2_pre_topc(k8_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_pre_topc(X32,X31))))&(l1_pre_topc(k8_tmap_1(X31,X32))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_pre_topc(X32,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 2.51/2.69  cnf(c_0_18, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.51/2.69  cnf(c_0_19, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.51/2.69  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.51/2.69  cnf(c_0_21, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.51/2.69  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.51/2.69  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.51/2.69  fof(c_0_24, plain, ![X13]:((~v2_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))|(v2_struct_0(X13)|~l1_pre_topc(X13)))&(v1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))|(v2_struct_0(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).
% 2.51/2.69  fof(c_0_25, plain, ![X20, X21, X22, X23]:((X22!=k8_tmap_1(X20,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(X23!=u1_struct_0(X21)|X22=k6_tmap_1(X20,X23)))|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))|X22=k8_tmap_1(X20,X21)|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((esk1_3(X20,X21,X22)=u1_struct_0(X21)|X22=k8_tmap_1(X20,X21)|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(X22!=k6_tmap_1(X20,esk1_3(X20,X21,X22))|X22=k8_tmap_1(X20,X21)|(~v1_pre_topc(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 2.51/2.69  fof(c_0_26, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_pre_topc(X42,X41)|m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 2.51/2.69  cnf(c_0_27, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 2.51/2.69  cnf(c_0_28, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.51/2.69  fof(c_0_29, plain, ![X7]:(~l1_pre_topc(X7)|(~v1_pre_topc(X7)|X7=g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 2.51/2.69  cnf(c_0_30, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 2.51/2.69  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.51/2.69  cnf(c_0_32, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.51/2.69  fof(c_0_33, plain, ![X37, X38]:((u1_struct_0(k6_tmap_1(X37,X38))=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(u1_pre_topc(k6_tmap_1(X37,X38))=k5_tmap_1(X37,X38)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 2.51/2.69  cnf(c_0_34, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.51/2.69  cnf(c_0_35, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.51/2.69  cnf(c_0_36, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.51/2.69  cnf(c_0_37, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.51/2.69  fof(c_0_38, plain, ![X25, X26, X27]:((~v1_tsep_1(X26,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(X27!=u1_struct_0(X26)|v3_pre_topc(X27,X25)))|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&((m1_subset_1(esk2_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))|v1_tsep_1(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&((esk2_2(X25,X26)=u1_struct_0(X26)|v1_tsep_1(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))&(~v3_pre_topc(esk2_2(X25,X26),X25)|v1_tsep_1(X26,X25)|~m1_pre_topc(X26,X25)|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 2.51/2.69  fof(c_0_39, plain, ![X8, X9]:((~v3_pre_topc(X9,X8)|r2_hidden(X9,u1_pre_topc(X8))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))&(~r2_hidden(X9,u1_pre_topc(X8))|v3_pre_topc(X9,X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 2.51/2.69  fof(c_0_40, plain, ![X35, X36]:((~r2_hidden(X36,u1_pre_topc(X35))|u1_pre_topc(X35)=k5_tmap_1(X35,X36)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(u1_pre_topc(X35)!=k5_tmap_1(X35,X36)|r2_hidden(X36,u1_pre_topc(X35))|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 2.51/2.69  cnf(c_0_41, negated_conjecture, (u1_pre_topc(esk3_0)=X1|v1_tsep_1(esk4_0,esk3_0)|k8_tmap_1(esk3_0,esk4_0)!=g1_pre_topc(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23])])).
% 2.51/2.69  cnf(c_0_42, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.51/2.69  cnf(c_0_43, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.51/2.69  cnf(c_0_44, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_23])]), c_0_20])).
% 2.51/2.69  cnf(c_0_45, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.51/2.69  cnf(c_0_46, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])]), c_0_35]), c_0_21]), c_0_36]), c_0_37])).
% 2.51/2.69  fof(c_0_47, plain, ![X29, X30]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|k6_tmap_1(X29,X30)=g1_pre_topc(u1_struct_0(X29),k5_tmap_1(X29,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 2.51/2.69  cnf(c_0_48, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.51/2.69  cnf(c_0_49, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.51/2.69  cnf(c_0_50, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.51/2.69  cnf(c_0_51, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.51/2.69  cnf(c_0_52, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))=u1_pre_topc(esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42])]), c_0_43])]), c_0_44])).
% 2.51/2.69  cnf(c_0_53, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_35])).
% 2.51/2.69  cnf(c_0_54, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.51/2.69  cnf(c_0_55, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.51/2.69  cnf(c_0_56, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.51/2.69  cnf(c_0_57, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~r2_hidden(esk2_2(X2,X1),u1_pre_topc(X2))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 2.51/2.69  cnf(c_0_58, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.51/2.69  cnf(c_0_59, plain, (v2_struct_0(X1)|r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))|k5_tmap_1(X1,u1_struct_0(X2))!=u1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_35])).
% 2.51/2.69  cnf(c_0_60, negated_conjecture, (k5_tmap_1(esk3_0,u1_struct_0(esk4_0))=u1_pre_topc(esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_22]), c_0_31]), c_0_23])]), c_0_20])).
% 2.51/2.69  cnf(c_0_61, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_31])])).
% 2.51/2.69  cnf(c_0_62, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.51/2.69  cnf(c_0_63, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 2.51/2.69  cnf(c_0_64, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22]), c_0_31]), c_0_23])]), c_0_20])).
% 2.51/2.69  cnf(c_0_65, negated_conjecture, (k6_tmap_1(esk3_0,X1)!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_22]), c_0_23])]), c_0_20])).
% 2.51/2.69  cnf(c_0_66, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_31]), c_0_23])])).
% 2.51/2.69  cnf(c_0_67, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 2.51/2.69  cnf(c_0_68, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.51/2.69  cnf(c_0_69, negated_conjecture, (k6_tmap_1(esk3_0,X1)!=k8_tmap_1(esk3_0,esk4_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 2.51/2.69  cnf(c_0_70, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_67, c_0_35])).
% 2.51/2.69  cnf(c_0_71, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]), c_0_35])).
% 2.51/2.69  cnf(c_0_72, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(X1))!=k8_tmap_1(esk3_0,esk4_0)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_35]), c_0_23])])).
% 2.51/2.69  cnf(c_0_73, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.51/2.69  cnf(c_0_74, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(X1))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(X1,esk3_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_23])])).
% 2.51/2.69  cnf(c_0_75, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_66]), c_0_31])])).
% 2.51/2.69  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_46]), c_0_22]), c_0_31]), c_0_23])]), c_0_20]), ['proof']).
% 2.51/2.69  # SZS output end CNFRefutation
% 2.51/2.69  # Proof object total steps             : 77
% 2.51/2.69  # Proof object clause steps            : 50
% 2.51/2.69  # Proof object formula steps           : 27
% 2.51/2.69  # Proof object conjectures             : 24
% 2.51/2.69  # Proof object clause conjectures      : 21
% 2.51/2.69  # Proof object formula conjectures     : 3
% 2.51/2.69  # Proof object initial clauses used    : 25
% 2.51/2.69  # Proof object initial formulas used   : 13
% 2.51/2.69  # Proof object generating inferences   : 21
% 2.51/2.69  # Proof object simplifying inferences  : 54
% 2.51/2.69  # Training examples: 0 positive, 0 negative
% 2.51/2.69  # Parsed axioms                        : 21
% 2.51/2.69  # Removed by relevancy pruning/SinE    : 0
% 2.51/2.69  # Initial clauses                      : 43
% 2.51/2.69  # Removed in clause preprocessing      : 0
% 2.51/2.69  # Initial clauses in saturation        : 43
% 2.51/2.69  # Processed clauses                    : 6413
% 2.51/2.69  # ...of these trivial                  : 181
% 2.51/2.69  # ...subsumed                          : 3762
% 2.51/2.69  # ...remaining for further processing  : 2470
% 2.51/2.69  # Other redundant clauses eliminated   : 3189
% 2.51/2.69  # Clauses deleted for lack of memory   : 0
% 2.51/2.69  # Backward-subsumed                    : 707
% 2.51/2.69  # Backward-rewritten                   : 944
% 2.51/2.69  # Generated clauses                    : 155476
% 2.51/2.69  # ...of the previous two non-trivial   : 142869
% 2.51/2.69  # Contextual simplify-reflections      : 229
% 2.51/2.69  # Paramodulations                      : 152261
% 2.51/2.69  # Factorizations                       : 4
% 2.51/2.69  # Equation resolutions                 : 3212
% 2.51/2.69  # Propositional unsat checks           : 0
% 2.51/2.69  #    Propositional check models        : 0
% 2.51/2.69  #    Propositional check unsatisfiable : 0
% 2.51/2.69  #    Propositional clauses             : 0
% 2.51/2.69  #    Propositional clauses after purity: 0
% 2.51/2.69  #    Propositional unsat core size     : 0
% 2.51/2.69  #    Propositional preprocessing time  : 0.000
% 2.51/2.69  #    Propositional encoding time       : 0.000
% 2.51/2.69  #    Propositional solver time         : 0.000
% 2.51/2.69  #    Success case prop preproc time    : 0.000
% 2.51/2.69  #    Success case prop encoding time   : 0.000
% 2.51/2.69  #    Success case prop solver time     : 0.000
% 2.51/2.69  # Current number of processed clauses  : 775
% 2.51/2.69  #    Positive orientable unit clauses  : 75
% 2.51/2.69  #    Positive unorientable unit clauses: 0
% 2.51/2.69  #    Negative unit clauses             : 4
% 2.51/2.69  #    Non-unit-clauses                  : 696
% 2.51/2.69  # Current number of unprocessed clauses: 136014
% 2.51/2.69  # ...number of literals in the above   : 1552331
% 2.51/2.69  # Current number of archived formulas  : 0
% 2.51/2.69  # Current number of archived clauses   : 1693
% 2.51/2.69  # Clause-clause subsumption calls (NU) : 464822
% 2.51/2.69  # Rec. Clause-clause subsumption calls : 97439
% 2.51/2.69  # Non-unit clause-clause subsumptions  : 4272
% 2.51/2.69  # Unit Clause-clause subsumption calls : 6593
% 2.51/2.69  # Rewrite failures with RHS unbound    : 0
% 2.51/2.69  # BW rewrite match attempts            : 1484
% 2.51/2.69  # BW rewrite match successes           : 50
% 2.51/2.69  # Condensation attempts                : 0
% 2.51/2.69  # Condensation successes               : 0
% 2.51/2.69  # Termbank termtop insertions          : 4992210
% 2.51/2.70  
% 2.51/2.70  # -------------------------------------------------
% 2.51/2.70  # User time                : 2.264 s
% 2.51/2.70  # System time              : 0.089 s
% 2.51/2.70  # Total time               : 2.353 s
% 2.51/2.70  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
