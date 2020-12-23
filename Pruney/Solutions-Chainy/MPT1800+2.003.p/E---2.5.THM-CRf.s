%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:22 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 394 expanded)
%              Number of clauses        :   49 ( 140 expanded)
%              Number of leaves         :   13 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  386 (2646 expanded)
%              Number of equality atoms :   67 ( 414 expanded)
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

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

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
    ! [X22,X23,X24,X25] :
      ( ( X22 = X24
        | g1_pre_topc(X22,X23) != g1_pre_topc(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) )
      & ( X23 = X25
        | g1_pre_topc(X22,X23) != g1_pre_topc(X24,X25)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_15,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19)))) ) ),
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
    ! [X21] :
      ( ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) )
      & ( v1_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | v2_struct_0(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).

fof(c_0_25,plain,(
    ! [X26,X27,X28,X29] :
      ( ( X28 != k8_tmap_1(X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | X29 != u1_struct_0(X27)
        | X28 = k6_tmap_1(X26,X29)
        | ~ v1_pre_topc(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk1_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))
        | X28 = k8_tmap_1(X26,X27)
        | ~ v1_pre_topc(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( esk1_3(X26,X27,X28) = u1_struct_0(X27)
        | X28 = k8_tmap_1(X26,X27)
        | ~ v1_pre_topc(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( X28 != k6_tmap_1(X26,esk1_3(X26,X27,X28))
        | X28 = k8_tmap_1(X26,X27)
        | ~ v1_pre_topc(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_26,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))) ) ),
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
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | ~ v1_pre_topc(X13)
      | X13 = g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)) ) ),
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
    ! [X41,X42] :
      ( ( u1_struct_0(k6_tmap_1(X41,X42)) = u1_struct_0(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( u1_pre_topc(k6_tmap_1(X41,X42)) = k5_tmap_1(X41,X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
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
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | k6_tmap_1(X35,X36) = g1_pre_topc(u1_struct_0(X35),k5_tmap_1(X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

fof(c_0_39,plain,(
    ! [X39,X40] :
      ( ( ~ r2_hidden(X40,u1_pre_topc(X39))
        | u1_pre_topc(X39) = k5_tmap_1(X39,X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( u1_pre_topc(X39) != k5_tmap_1(X39,X40)
        | r2_hidden(X40,u1_pre_topc(X39))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_40,negated_conjecture,
    ( u1_pre_topc(esk3_0) = X1
    | v1_tsep_1(esk4_0,esk3_0)
    | k8_tmap_1(esk3_0,esk4_0) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_23])])).

cnf(c_0_41,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_28]),c_0_23])]),c_0_20])).

cnf(c_0_44,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])]),c_0_35]),c_0_21]),c_0_36]),c_0_37])).

fof(c_0_46,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v1_tsep_1(X32,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | X33 != u1_struct_0(X32)
        | v3_pre_topc(X33,X31)
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk2_2(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))
        | v1_tsep_1(X32,X31)
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) )
      & ( esk2_2(X31,X32) = u1_struct_0(X32)
        | v1_tsep_1(X32,X31)
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ v3_pre_topc(esk2_2(X31,X32),X31)
        | v1_tsep_1(X32,X31)
        | ~ m1_pre_topc(X32,X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) = u1_pre_topc(esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41])]),c_0_42])]),c_0_43])).

cnf(c_0_52,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35])).

cnf(c_0_53,plain,
    ( v1_tsep_1(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X14,X15] :
      ( ( ~ v3_pre_topc(X15,X14)
        | r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(X15,u1_pre_topc(X14))
        | v3_pre_topc(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_56,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_31])])).

cnf(c_0_57,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))
    | k5_tmap_1(X1,u1_struct_0(X2)) != u1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( k5_tmap_1(esk3_0,u1_struct_0(esk4_0)) = u1_pre_topc(esk3_0)
    | v1_tsep_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22]),c_0_31]),c_0_23])]),c_0_20])).

cnf(c_0_60,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k6_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_tsep_1(esk4_0,esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_22]),c_0_23])]),c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk3_0)
    | r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_22]),c_0_31]),c_0_23])]),c_0_20])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_66,plain,
    ( v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))
    | k6_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_35])).

cnf(c_0_69,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_65]),c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( k6_tmap_1(esk3_0,X1) != k8_tmap_1(esk3_0,esk4_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_66]),c_0_31]),c_0_23])]),c_0_67])).

cnf(c_0_71,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) != k8_tmap_1(esk3_0,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_35]),c_0_23])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_63]),c_0_31]),c_0_23])])).

cnf(c_0_74,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) != k8_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_31])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_45]),c_0_22]),c_0_31]),c_0_23])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 1.06/1.25  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.06/1.25  # and selection function PSelectUnlessUniqMaxPos.
% 1.06/1.25  #
% 1.06/1.25  # Preprocessing time       : 0.029 s
% 1.06/1.25  # Presaturation interreduction done
% 1.06/1.25  
% 1.06/1.25  # Proof found!
% 1.06/1.25  # SZS status Theorem
% 1.06/1.25  # SZS output start CNFRefutation
% 1.06/1.25  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 1.06/1.25  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 1.06/1.25  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 1.06/1.25  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 1.06/1.25  fof(fc7_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>(~(v2_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))&v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 1.06/1.25  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 1.06/1.25  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.06/1.25  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 1.06/1.25  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 1.06/1.25  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 1.06/1.25  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 1.06/1.25  fof(d1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tsep_1(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 1.06/1.25  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 1.06/1.25  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 1.06/1.25  fof(c_0_14, plain, ![X22, X23, X24, X25]:((X22=X24|g1_pre_topc(X22,X23)!=g1_pre_topc(X24,X25)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))))&(X23=X25|g1_pre_topc(X22,X23)!=g1_pre_topc(X24,X25)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 1.06/1.25  fof(c_0_15, plain, ![X19]:(~l1_pre_topc(X19)|m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 1.06/1.25  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0))&((v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0))&(m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).
% 1.06/1.25  fof(c_0_17, plain, ![X37, X38]:(((v1_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))&(v2_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37))))&(l1_pre_topc(k8_tmap_1(X37,X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|~m1_pre_topc(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 1.06/1.25  cnf(c_0_18, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.06/1.25  cnf(c_0_19, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.06/1.25  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.06/1.25  cnf(c_0_21, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.06/1.25  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.06/1.25  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.06/1.25  fof(c_0_24, plain, ![X21]:((~v2_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(v2_struct_0(X21)|~l1_pre_topc(X21)))&(v1_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(v2_struct_0(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_pre_topc])])])])).
% 1.06/1.25  fof(c_0_25, plain, ![X26, X27, X28, X29]:((X28!=k8_tmap_1(X26,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|(X29!=u1_struct_0(X27)|X28=k6_tmap_1(X26,X29)))|(~v1_pre_topc(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~m1_pre_topc(X27,X26)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((m1_subset_1(esk1_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))|X28=k8_tmap_1(X26,X27)|(~v1_pre_topc(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~m1_pre_topc(X27,X26)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((esk1_3(X26,X27,X28)=u1_struct_0(X27)|X28=k8_tmap_1(X26,X27)|(~v1_pre_topc(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~m1_pre_topc(X27,X26)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(X28!=k6_tmap_1(X26,esk1_3(X26,X27,X28))|X28=k8_tmap_1(X26,X27)|(~v1_pre_topc(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~m1_pre_topc(X27,X26)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 1.06/1.25  fof(c_0_26, plain, ![X45, X46]:(~l1_pre_topc(X45)|(~m1_pre_topc(X46,X45)|m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 1.06/1.25  cnf(c_0_27, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.06/1.25  cnf(c_0_28, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.06/1.25  fof(c_0_29, plain, ![X13]:(~l1_pre_topc(X13)|(~v1_pre_topc(X13)|X13=g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 1.06/1.25  cnf(c_0_30, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 1.06/1.25  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.06/1.25  cnf(c_0_32, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|v2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.06/1.25  fof(c_0_33, plain, ![X41, X42]:((u1_struct_0(k6_tmap_1(X41,X42))=u1_struct_0(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(u1_pre_topc(k6_tmap_1(X41,X42))=k5_tmap_1(X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 1.06/1.25  cnf(c_0_34, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.06/1.25  cnf(c_0_35, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.06/1.25  cnf(c_0_36, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.06/1.25  cnf(c_0_37, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.06/1.25  fof(c_0_38, plain, ![X35, X36]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|k6_tmap_1(X35,X36)=g1_pre_topc(u1_struct_0(X35),k5_tmap_1(X35,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 1.06/1.25  fof(c_0_39, plain, ![X39, X40]:((~r2_hidden(X40,u1_pre_topc(X39))|u1_pre_topc(X39)=k5_tmap_1(X39,X40)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(u1_pre_topc(X39)!=k5_tmap_1(X39,X40)|r2_hidden(X40,u1_pre_topc(X39))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 1.06/1.25  cnf(c_0_40, negated_conjecture, (u1_pre_topc(esk3_0)=X1|v1_tsep_1(esk4_0,esk3_0)|k8_tmap_1(esk3_0,esk4_0)!=g1_pre_topc(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_23])])).
% 1.06/1.25  cnf(c_0_41, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.06/1.25  cnf(c_0_42, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.06/1.25  cnf(c_0_43, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_28]), c_0_23])]), c_0_20])).
% 1.06/1.25  cnf(c_0_44, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.06/1.25  cnf(c_0_45, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])]), c_0_35]), c_0_21]), c_0_36]), c_0_37])).
% 1.06/1.25  fof(c_0_46, plain, ![X31, X32, X33]:((~v1_tsep_1(X32,X31)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(X33!=u1_struct_0(X32)|v3_pre_topc(X33,X31)))|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31))&((m1_subset_1(esk2_2(X31,X32),k1_zfmisc_1(u1_struct_0(X31)))|v1_tsep_1(X32,X31)|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31))&((esk2_2(X31,X32)=u1_struct_0(X32)|v1_tsep_1(X32,X31)|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31))&(~v3_pre_topc(esk2_2(X31,X32),X31)|v1_tsep_1(X32,X31)|~m1_pre_topc(X32,X31)|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tsep_1])])])])])).
% 1.06/1.25  cnf(c_0_47, negated_conjecture, (~v1_tsep_1(esk4_0,esk3_0)|~m1_pre_topc(esk4_0,esk3_0)|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.06/1.25  cnf(c_0_48, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.06/1.25  cnf(c_0_49, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.06/1.25  cnf(c_0_50, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.06/1.25  cnf(c_0_51, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))=u1_pre_topc(esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41])]), c_0_42])]), c_0_43])).
% 1.06/1.25  cnf(c_0_52, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35])).
% 1.06/1.25  cnf(c_0_53, plain, (v1_tsep_1(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.06/1.25  cnf(c_0_54, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.06/1.25  fof(c_0_55, plain, ![X14, X15]:((~v3_pre_topc(X15,X14)|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~r2_hidden(X15,u1_pre_topc(X14))|v3_pre_topc(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 1.06/1.25  cnf(c_0_56, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_31])])).
% 1.06/1.25  cnf(c_0_57, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.06/1.25  cnf(c_0_58, plain, (v2_struct_0(X1)|r2_hidden(u1_struct_0(X2),u1_pre_topc(X1))|k5_tmap_1(X1,u1_struct_0(X2))!=u1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 1.06/1.25  cnf(c_0_59, negated_conjecture, (k5_tmap_1(esk3_0,u1_struct_0(esk4_0))=u1_pre_topc(esk3_0)|v1_tsep_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_22]), c_0_31]), c_0_23])]), c_0_20])).
% 1.06/1.25  cnf(c_0_60, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.06/1.25  cnf(c_0_61, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.06/1.25  cnf(c_0_62, negated_conjecture, (k6_tmap_1(esk3_0,X1)!=k8_tmap_1(esk3_0,esk4_0)|~v1_tsep_1(esk4_0,esk3_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_22]), c_0_23])]), c_0_20])).
% 1.06/1.25  cnf(c_0_63, negated_conjecture, (v1_tsep_1(esk4_0,esk3_0)|r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_22]), c_0_31]), c_0_23])]), c_0_20])).
% 1.06/1.25  cnf(c_0_64, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.06/1.25  cnf(c_0_65, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.06/1.25  cnf(c_0_66, plain, (v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_35])).
% 1.06/1.25  cnf(c_0_67, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))|k6_tmap_1(esk3_0,X1)!=k8_tmap_1(esk3_0,esk4_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.06/1.25  cnf(c_0_68, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_64, c_0_35])).
% 1.06/1.25  cnf(c_0_69, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_65]), c_0_35])).
% 1.06/1.25  cnf(c_0_70, negated_conjecture, (k6_tmap_1(esk3_0,X1)!=k8_tmap_1(esk3_0,esk4_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_66]), c_0_31]), c_0_23])]), c_0_67])).
% 1.06/1.25  cnf(c_0_71, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.06/1.25  cnf(c_0_72, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(X1))!=k8_tmap_1(esk3_0,esk4_0)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_35]), c_0_23])])).
% 1.06/1.25  cnf(c_0_73, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_63]), c_0_31]), c_0_23])])).
% 1.06/1.25  cnf(c_0_74, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))!=k8_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_31])])).
% 1.06/1.25  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_45]), c_0_22]), c_0_31]), c_0_23])]), c_0_20]), ['proof']).
% 1.06/1.25  # SZS output end CNFRefutation
% 1.06/1.25  # Proof object total steps             : 76
% 1.06/1.25  # Proof object clause steps            : 49
% 1.06/1.25  # Proof object formula steps           : 27
% 1.06/1.25  # Proof object conjectures             : 24
% 1.06/1.25  # Proof object clause conjectures      : 21
% 1.06/1.25  # Proof object formula conjectures     : 3
% 1.06/1.25  # Proof object initial clauses used    : 24
% 1.06/1.25  # Proof object initial formulas used   : 13
% 1.06/1.25  # Proof object generating inferences   : 22
% 1.06/1.25  # Proof object simplifying inferences  : 54
% 1.06/1.25  # Training examples: 0 positive, 0 negative
% 1.06/1.25  # Parsed axioms                        : 24
% 1.06/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.06/1.25  # Initial clauses                      : 49
% 1.06/1.25  # Removed in clause preprocessing      : 0
% 1.06/1.25  # Initial clauses in saturation        : 49
% 1.06/1.25  # Processed clauses                    : 3517
% 1.06/1.25  # ...of these trivial                  : 18
% 1.06/1.25  # ...subsumed                          : 1989
% 1.06/1.25  # ...remaining for further processing  : 1510
% 1.06/1.25  # Other redundant clauses eliminated   : 711
% 1.06/1.25  # Clauses deleted for lack of memory   : 0
% 1.06/1.25  # Backward-subsumed                    : 309
% 1.06/1.25  # Backward-rewritten                   : 14
% 1.06/1.25  # Generated clauses                    : 51567
% 1.06/1.25  # ...of the previous two non-trivial   : 49295
% 1.06/1.25  # Contextual simplify-reflections      : 220
% 1.06/1.25  # Paramodulations                      : 50814
% 1.06/1.25  # Factorizations                       : 12
% 1.06/1.25  # Equation resolutions                 : 742
% 1.06/1.25  # Propositional unsat checks           : 0
% 1.06/1.25  #    Propositional check models        : 0
% 1.06/1.25  #    Propositional check unsatisfiable : 0
% 1.06/1.25  #    Propositional clauses             : 0
% 1.06/1.25  #    Propositional clauses after purity: 0
% 1.06/1.25  #    Propositional unsat core size     : 0
% 1.06/1.25  #    Propositional preprocessing time  : 0.000
% 1.06/1.25  #    Propositional encoding time       : 0.000
% 1.06/1.25  #    Propositional solver time         : 0.000
% 1.06/1.25  #    Success case prop preproc time    : 0.000
% 1.06/1.25  #    Success case prop encoding time   : 0.000
% 1.06/1.25  #    Success case prop solver time     : 0.000
% 1.06/1.25  # Current number of processed clauses  : 1139
% 1.06/1.25  #    Positive orientable unit clauses  : 25
% 1.06/1.25  #    Positive unorientable unit clauses: 0
% 1.06/1.25  #    Negative unit clauses             : 3
% 1.06/1.25  #    Non-unit-clauses                  : 1111
% 1.06/1.25  # Current number of unprocessed clauses: 45720
% 1.06/1.25  # ...number of literals in the above   : 525736
% 1.06/1.25  # Current number of archived formulas  : 0
% 1.06/1.25  # Current number of archived clauses   : 369
% 1.06/1.25  # Clause-clause subsumption calls (NU) : 261086
% 1.06/1.25  # Rec. Clause-clause subsumption calls : 74389
% 1.06/1.25  # Non-unit clause-clause subsumptions  : 2504
% 1.06/1.25  # Unit Clause-clause subsumption calls : 1581
% 1.06/1.25  # Rewrite failures with RHS unbound    : 0
% 1.06/1.25  # BW rewrite match attempts            : 148
% 1.06/1.25  # BW rewrite match successes           : 8
% 1.06/1.25  # Condensation attempts                : 0
% 1.06/1.25  # Condensation successes               : 0
% 1.06/1.25  # Termbank termtop insertions          : 1777771
% 1.06/1.25  
% 1.06/1.25  # -------------------------------------------------
% 1.06/1.25  # User time                : 0.864 s
% 1.06/1.25  # System time              : 0.037 s
% 1.06/1.25  # Total time               : 0.901 s
% 1.06/1.25  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
