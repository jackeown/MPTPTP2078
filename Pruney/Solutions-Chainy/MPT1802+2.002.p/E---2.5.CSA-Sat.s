%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:25 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  465 (28582 expanded)
%              Number of clauses        :  434 (9386 expanded)
%              Number of leaves         :   15 (7077 expanded)
%              Depth                    :   14
%              Number of atoms          : 2727 (209244 expanded)
%              Number of equality atoms :  297 (5682 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t117_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_tmap_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
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
      & ( m1_subset_1(esk1_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))
        | X21 = k8_tmap_1(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( esk1_3(X19,X20,X21) = u1_struct_0(X20)
        | X21 = k8_tmap_1(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( X21 != k6_tmap_1(X19,esk1_3(X19,X20,X21))
        | X21 = k8_tmap_1(X19,X20)
        | ~ v1_pre_topc(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & r1_tsep_1(esk3_0,esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( v1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( v2_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( l1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_19,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k7_tmap_1(X17,X18) = k6_partfun1(u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_20,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_21,plain,(
    ! [X32,X33,X34,X35] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | v2_struct_0(X34)
      | ~ m1_pre_topc(X34,X32)
      | ~ r1_xboole_0(u1_struct_0(X34),X33)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | r1_tmap_1(X34,k6_tmap_1(X32,X33),k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).

fof(c_0_22,plain,(
    ! [X36,X37,X38] :
      ( ( u1_struct_0(k8_tmap_1(X36,X37)) = u1_struct_0(X36)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | X38 != u1_struct_0(X37)
        | u1_pre_topc(k8_tmap_1(X36,X37)) = k5_tmap_1(X36,X38)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_28,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_30,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_31,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_32,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_34,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ( ~ r1_tsep_1(X24,X25)
        | r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X24) )
      & ( ~ r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))
        | r1_tsep_1(X24,X25)
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_37,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( X1 = k8_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( esk1_3(esk2_0,esk3_0,X1) = u1_struct_0(esk3_0)
    | X1 = k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k8_tmap_1(esk2_0,esk4_0)
    | m1_subset_1(esk1_3(esk2_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( esk1_3(esk2_0,esk4_0,X1) = u1_struct_0(esk4_0)
    | X1 = k8_tmap_1(esk2_0,esk4_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_50,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34]),
    [final]).

cnf(c_0_51,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X3)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X3)),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X3))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34]),
    [final]).

cnf(c_0_52,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

fof(c_0_53,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_54,plain,(
    ! [X30,X31] :
      ( ~ l1_struct_0(X30)
      | ~ l1_struct_0(X31)
      | ~ r1_tsep_1(X30,X31)
      | r1_tsep_1(X31,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_55,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk4_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_25]),c_0_26])]),c_0_38]),c_0_27]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)) = u1_struct_0(esk3_0)
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_41]),c_0_42])]),
    [final]).

cnf(c_0_59,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])]),c_0_31]),c_0_34]),c_0_30]),c_0_28]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk4_0)
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_47]),c_0_48])]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_63,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X3)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X3)),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_65,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_66,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_68,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk4_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_62]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_38])).

cnf(c_0_76,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_26])]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_25]),c_0_26])]),c_0_67]),c_0_27]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( r1_tsep_1(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ r1_tsep_1(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( r1_tsep_1(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_70]),c_0_71]),c_0_71]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_72]),c_0_73]),c_0_73]),c_0_25]),c_0_26])]),c_0_27]),c_0_74]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r1_tsep_1(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_78]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_79]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_80]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_24]),c_0_26])]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_78]),c_0_78]),c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_80]),c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_96,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_78]),c_0_47]),c_0_48])]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),X2),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),X2),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),X2),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_56]),c_0_41]),c_0_42])]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_78]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_76]),c_0_77])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_76]),c_0_77])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_76]),c_0_92])])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_56]),c_0_42])]),
    [final]).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_78]),c_0_48])]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_70]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_111,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_72]),
    [final]).

cnf(c_0_112,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_70]),
    [final]).

cnf(c_0_113,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_72]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_52]),
    [final]).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_78]),
    [final]).

cnf(c_0_116,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_78])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_56]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_56])).

cnf(c_0_119,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_78])).

cnf(c_0_120,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_56])).

fof(c_0_121,plain,(
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

fof(c_0_122,plain,(
    ! [X28,X29] :
      ( ( v1_funct_1(k9_tmap_1(X28,X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( v1_funct_2(k9_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( m1_subset_1(k9_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_78])).

cnf(c_0_124,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_56])).

cnf(c_0_125,negated_conjecture,
    ( r1_tsep_1(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_103]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_107]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_130,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_108]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_131,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_56]),
    [final]).

cnf(c_0_132,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_52]),
    [final]).

cnf(c_0_133,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_56]),
    [final]).

cnf(c_0_134,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_78]),
    [final]).

cnf(c_0_135,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_78]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_78]),
    [final]).

cnf(c_0_137,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_114])).

cnf(c_0_138,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_78]),
    [final]).

cnf(c_0_139,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_56]),
    [final]).

cnf(c_0_140,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_56]),
    [final]).

cnf(c_0_141,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_115]),
    [final]).

cnf(c_0_142,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_143,negated_conjecture,
    ( r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_86]),
    [final]).

cnf(c_0_144,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_117]),
    [final]).

cnf(c_0_145,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_146,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_147,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_148,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_78]),
    [final]).

cnf(c_0_149,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_56]),
    [final]).

cnf(c_0_150,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_78]),
    [final]).

cnf(c_0_151,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_152,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122]),
    [final]).

cnf(c_0_153,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122]),
    [final]).

cnf(c_0_154,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_122]),
    [final]).

cnf(c_0_155,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_56]),
    [final]).

cnf(c_0_156,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),X1) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_56]),c_0_41]),c_0_42])])).

cnf(c_0_157,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_78]),c_0_47]),c_0_48])])).

fof(c_0_158,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_159,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_160,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_161,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_125]),c_0_78]),c_0_78]),c_0_78])).

cnf(c_0_162,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_114])).

cnf(c_0_163,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_52])).

cnf(c_0_164,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_82]),c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_165,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_114])).

cnf(c_0_166,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_52])).

cnf(c_0_167,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_29]),c_0_71]),c_0_71]),c_0_25]),c_0_24]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_168,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_169,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_170,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_171,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_131,c_0_52])).

cnf(c_0_172,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_132])).

cnf(c_0_173,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_52])).

cnf(c_0_174,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_132])).

cnf(c_0_175,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_52])).

cnf(c_0_176,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_132])).

cnf(c_0_177,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_52])).

cnf(c_0_178,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_132])).

cnf(c_0_179,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_180,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_52])).

cnf(c_0_181,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_132])).

cnf(c_0_182,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_52])).

cnf(c_0_183,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_132])).

cnf(c_0_184,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_52])).

cnf(c_0_185,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_132])).

cnf(c_0_186,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_78]),
    [final]).

cnf(c_0_187,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_132]),c_0_27])).

cnf(c_0_188,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_56]),
    [final]).

cnf(c_0_189,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_132]),c_0_27])).

cnf(c_0_190,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_52])).

cnf(c_0_191,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_132]),c_0_27])).

cnf(c_0_192,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_132]),c_0_27])).

cnf(c_0_193,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_141,c_0_78]),
    [final]).

cnf(c_0_194,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_195,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_144,c_0_56]),
    [final]).

cnf(c_0_196,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_89])).

cnf(c_0_197,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_143])).

cnf(c_0_198,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_147,c_0_89])).

cnf(c_0_199,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_132])).

cnf(c_0_200,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_52])).

cnf(c_0_201,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_132])).

cnf(c_0_202,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_52])).

cnf(c_0_203,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_132])).

cnf(c_0_204,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_52])).

cnf(c_0_205,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_132]),c_0_27])).

cnf(c_0_206,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_114]),
    [final]).

cnf(c_0_207,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[c_0_151]),
    [final]).

cnf(c_0_208,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_24]),c_0_78]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_209,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_24]),c_0_78]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_210,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_211,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_132])).

cnf(c_0_212,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_29]),c_0_56]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_213,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_29]),c_0_56]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_214,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_215,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_52])).

cnf(c_0_216,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_132]),c_0_27])).

cnf(c_0_217,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_34]),c_0_26])])).

cnf(c_0_218,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_34]),c_0_26])])).

cnf(c_0_219,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_158]),
    [final]).

fof(c_0_220,plain,(
    ! [X39,X40] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ m1_pre_topc(X40,X39)
      | r1_funct_2(u1_struct_0(X39),u1_struct_0(k8_tmap_1(X39,X40)),u1_struct_0(X39),u1_struct_0(X39),k9_tmap_1(X39,X40),k3_struct_0(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_tmap_1])])])])).

cnf(c_0_221,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_222,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_159,c_0_143])).

cnf(c_0_223,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_160,c_0_89])).

cnf(c_0_224,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_76]),c_0_77])])).

cnf(c_0_225,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_76]),c_0_26])])).

cnf(c_0_226,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_76]),c_0_26])])).

cnf(c_0_227,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_76]),c_0_77])])).

cnf(c_0_228,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_76]),c_0_26])])).

cnf(c_0_229,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_76]),c_0_26])])).

cnf(c_0_230,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_57]),
    [final]).

cnf(c_0_231,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(X1)),esk4_0),esk5_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_167,c_0_168]),
    [final]).

cnf(c_0_232,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_60]),
    [final]).

cnf(c_0_233,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(X1)),esk4_0),esk5_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_167,c_0_169]),
    [final]).

cnf(c_0_234,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_57]),
    [final]).

cnf(c_0_235,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_60]),
    [final]).

cnf(c_0_236,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_57]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_237,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_76]),c_0_26])])).

cnf(c_0_238,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_76]),c_0_92])])).

cnf(c_0_239,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_76]),c_0_26])])).

cnf(c_0_240,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_76]),c_0_77])])).

cnf(c_0_241,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_52])).

cnf(c_0_242,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_60]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_243,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_76]),c_0_26])])).

cnf(c_0_244,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_52])).

cnf(c_0_245,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_52])).

cnf(c_0_246,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_52])).

cnf(c_0_247,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_76]),c_0_92])])).

cnf(c_0_248,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_76]),c_0_26])])).

cnf(c_0_249,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_76]),c_0_77])])).

cnf(c_0_250,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_76]),c_0_26])])).

cnf(c_0_251,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_179,c_0_78])).

cnf(c_0_252,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_76]),c_0_92])])).

cnf(c_0_253,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_76]),c_0_26])])).

cnf(c_0_254,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_179,c_0_56])).

cnf(c_0_255,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_76]),c_0_77])])).

cnf(c_0_256,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_76]),c_0_26])])).

cnf(c_0_257,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_76]),c_0_92])])).

cnf(c_0_258,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_76]),c_0_26])])).

cnf(c_0_259,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_186,c_0_132])).

cnf(c_0_260,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187,c_0_76]),c_0_26])])).

cnf(c_0_261,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_186,c_0_52])).

cnf(c_0_262,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_132])).

cnf(c_0_263,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_76]),c_0_26])])).

cnf(c_0_264,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_188,c_0_52])).

cnf(c_0_265,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_76]),c_0_77])])).

cnf(c_0_266,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_76]),c_0_26])])).

cnf(c_0_267,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_76]),c_0_26])])).

cnf(c_0_268,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_193,c_0_52])).

cnf(c_0_269,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_76]),c_0_92])])).

cnf(c_0_270,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_195,c_0_52])).

cnf(c_0_271,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196,c_0_76]),c_0_92])])).

cnf(c_0_272,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_141,c_0_114])).

cnf(c_0_273,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_76]),c_0_77])])).

cnf(c_0_274,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_141,c_0_52])).

cnf(c_0_275,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_144,c_0_114])).

cnf(c_0_276,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_76]),c_0_77])])).

cnf(c_0_277,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_144,c_0_52])).

cnf(c_0_278,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_76]),c_0_26])])).

cnf(c_0_279,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_76]),c_0_92])])).

cnf(c_0_280,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_64]),c_0_38])).

cnf(c_0_281,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_76]),c_0_26])])).

cnf(c_0_282,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202,c_0_76]),c_0_92])])).

cnf(c_0_283,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk4_0),esk5_0)
    | ~ r1_tsep_1(esk4_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_64]),c_0_29])]),c_0_38])).

cnf(c_0_284,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_76]),c_0_26])])).

cnf(c_0_285,negated_conjecture,
    ( r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk2_0),X3)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_132]),c_0_27])).

cnf(c_0_286,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_76]),c_0_77])])).

cnf(c_0_287,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205,c_0_76]),c_0_26])])).

cnf(c_0_288,negated_conjecture,
    ( r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk2_0),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_206]),c_0_27])).

cnf(c_0_289,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k9_tmap_1(esk2_0,esk3_0),X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_208]),c_0_209]),c_0_210])]),
    [final]).

cnf(c_0_290,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_76]),c_0_26])])).

cnf(c_0_291,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk4_0),k9_tmap_1(esk2_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(k9_tmap_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k9_tmap_1(esk2_0,esk4_0),X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_212]),c_0_213]),c_0_214])]),
    [final]).

cnf(c_0_292,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215,c_0_76]),c_0_77])])).

cnf(c_0_293,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,esk2_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216,c_0_76]),c_0_26])])).

cnf(c_0_294,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_168]),
    [final]).

cnf(c_0_295,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_296,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_169]),
    [final]).

cnf(c_0_297,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_121]),
    [final]).

cnf(c_0_298,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_299,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_107])).

cnf(c_0_300,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_108])).

cnf(c_0_301,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_107])).

cnf(c_0_302,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_108])).

cnf(c_0_303,negated_conjecture,
    ( k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))) = k6_partfun1(u1_struct_0(esk2_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_60]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_304,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_217,c_0_29])).

cnf(c_0_305,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_217,c_0_24])).

cnf(c_0_306,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_218,c_0_29])).

cnf(c_0_307,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_115]),c_0_26])])).

cnf(c_0_308,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_218,c_0_24])).

cnf(c_0_309,negated_conjecture,
    ( k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))) = k6_partfun1(u1_struct_0(esk2_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_57]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_310,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_117]),c_0_26])])).

cnf(c_0_311,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_115]),c_0_26])])).

cnf(c_0_312,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_117]),c_0_26])])).

cnf(c_0_313,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_56])).

cnf(c_0_314,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_78])).

cnf(c_0_315,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_56])).

cnf(c_0_316,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_78])).

cnf(c_0_317,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_129]),
    [final]).

cnf(c_0_318,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_219,c_0_78])).

cnf(c_0_319,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_219,c_0_56])).

cnf(c_0_320,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_220]),
    [final]).

cnf(c_0_321,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_221]),c_0_34]),
    [final]).

cnf(c_0_322,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_323,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_324,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_224,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_325,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_326,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_327,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_227,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_328,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_329,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_229,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_330,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_230,c_0_56]),
    [final]).

cnf(c_0_331,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_231,c_0_78]),
    [final]).

cnf(c_0_332,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_231,c_0_56]),
    [final]).

cnf(c_0_333,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_232,c_0_56]),
    [final]).

cnf(c_0_334,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_233,c_0_78]),
    [final]).

cnf(c_0_335,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_233,c_0_56]),
    [final]).

cnf(c_0_336,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_234,c_0_78]),
    [final]).

cnf(c_0_337,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_235,c_0_78]),
    [final]).

cnf(c_0_338,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_230,c_0_78]),
    [final]).

cnf(c_0_339,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_232,c_0_78]),
    [final]).

cnf(c_0_340,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_234,c_0_56]),
    [final]).

cnf(c_0_341,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_235,c_0_56]),
    [final]).

cnf(c_0_342,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_236,c_0_78]),
    [final]).

cnf(c_0_343,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_344,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_236,c_0_56]),
    [final]).

cnf(c_0_345,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_238,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_346,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_347,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_240,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_348,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_349,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_242,c_0_78]),
    [final]).

cnf(c_0_350,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_351,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_352,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_353,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_246,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_354,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_242,c_0_56]),
    [final]).

cnf(c_0_355,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_247,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_356,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_248,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_357,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_108]),
    [final]).

cnf(c_0_358,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_249,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_359,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_250,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_360,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_361,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_107]),
    [final]).

cnf(c_0_362,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_252,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_363,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_253,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_364,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk4_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_365,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_34]),c_0_26])]),
    [final]).

cnf(c_0_366,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_255,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_367,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_256,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_368,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_115]),c_0_26])]),
    [final]).

cnf(c_0_369,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_370,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_371,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_259,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_372,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_117]),c_0_26])]),
    [final]).

cnf(c_0_373,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_260,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_374,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_261,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_375,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_262,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_376,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_263,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_377,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_264,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_378,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_265,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_379,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_380,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),esk2_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_267,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_381,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_382,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_383,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_270,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_384,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_108]),
    [final]).

cnf(c_0_385,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_271,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_386,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_272,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_387,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_107]),
    [final]).

cnf(c_0_388,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_389,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_274,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_390,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_275,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_391,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),X1),X3)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_34]),c_0_26])]),
    [final]).

cnf(c_0_392,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_276,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_393,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk2_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_394,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_115]),c_0_26])]),
    [final]).

cnf(c_0_395,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_396,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_279,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_397,negated_conjecture,
    ( r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_280,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_398,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),X1),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_117]),c_0_26])]),
    [final]).

cnf(c_0_399,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_281,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_400,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_282,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_401,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk4_0),esk5_0)
    | ~ r1_tsep_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_402,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_403,negated_conjecture,
    ( r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk2_0),X3)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_285,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_404,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk2_0,u1_struct_0(X2)),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,u1_struct_0(X2)),k7_tmap_1(esk2_0,u1_struct_0(X2)),X1),X3)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_108]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_405,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk2_0,u1_struct_0(X2)),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,u1_struct_0(X2)),k7_tmap_1(esk2_0,u1_struct_0(X2)),X1),X3)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_107]),c_0_25]),c_0_26])]),c_0_27]),
    [final]).

cnf(c_0_406,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_407,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)
    | ~ r1_tsep_1(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_76]),c_0_92])]),
    [final]).

cnf(c_0_408,negated_conjecture,
    ( r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk2_0),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(esk2_0,esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_288,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_409,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289,c_0_208]),c_0_209])]),
    [final]).

cnf(c_0_410,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_290,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_411,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk4_0),k9_tmap_1(esk2_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_291,c_0_212]),c_0_213])]),
    [final]).

cnf(c_0_412,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ r1_tsep_1(esk2_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_292,c_0_76]),c_0_26])]),
    [final]).

cnf(c_0_413,negated_conjecture,
    ( k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)
    | ~ r1_tsep_1(esk4_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293,c_0_76]),c_0_77])]),
    [final]).

cnf(c_0_414,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_294,c_0_78]),
    [final]).

cnf(c_0_415,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(X1))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_294,c_0_56]),
    [final]).

cnf(c_0_416,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_294,c_0_78]),
    [final]).

cnf(c_0_417,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_294,c_0_56]),
    [final]).

cnf(c_0_418,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_295,c_0_57]),
    [final]).

cnf(c_0_419,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_296,c_0_78]),
    [final]).

cnf(c_0_420,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_296,c_0_56]),
    [final]).

cnf(c_0_421,negated_conjecture,
    ( X1 = k9_tmap_1(esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k9_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297,c_0_208]),c_0_209]),c_0_210])]),
    [final]).

cnf(c_0_422,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_295,c_0_60]),
    [final]).

cnf(c_0_423,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_298,c_0_57]),
    [final]).

cnf(c_0_424,negated_conjecture,
    ( X1 = k9_tmap_1(esk2_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k9_tmap_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297,c_0_212]),c_0_213]),c_0_214])]),
    [final]).

cnf(c_0_425,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_298,c_0_60]),
    [final]).

cnf(c_0_426,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_299,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_427,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_300,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_428,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_301,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_429,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_302,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_430,negated_conjecture,
    ( k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_303,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_431,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_304,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_432,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_305,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_433,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_306,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_434,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_307,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_435,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_217,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_436,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_218,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_437,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_308,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_438,negated_conjecture,
    ( k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | k8_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_309,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_439,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_310,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_440,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_311,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_441,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_312,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_442,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_313,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_443,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_314,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_444,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_315,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_445,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_316,c_0_62]),c_0_74]),
    [final]).

cnf(c_0_446,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_317,c_0_78]),
    [final]).

cnf(c_0_447,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_317,c_0_56]),
    [final]).

cnf(c_0_448,negated_conjecture,
    ( k6_partfun1(u1_struct_0(X1)) = k7_tmap_1(X1,u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_115]),
    [final]).

cnf(c_0_449,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_450,negated_conjecture,
    ( k6_partfun1(u1_struct_0(X1)) = k7_tmap_1(X1,u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_117]),
    [final]).

cnf(c_0_451,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_78]),
    [final]).

cnf(c_0_452,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ r1_tsep_1(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_78]),
    [final]).

cnf(c_0_453,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_78]),
    [final]).

cnf(c_0_454,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_56]),
    [final]).

cnf(c_0_455,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_78]),
    [final]).

cnf(c_0_456,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_56]),
    [final]).

cnf(c_0_457,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_318,c_0_76]),c_0_48])]),
    [final]).

cnf(c_0_458,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk4_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_319,c_0_76]),c_0_42])]),
    [final]).

cnf(c_0_459,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_460,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_74]),
    [final]).

cnf(c_0_461,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_320,c_0_24]),c_0_78]),c_0_25]),c_0_26])]),c_0_67]),c_0_27]),
    [final]).

cnf(c_0_462,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk4_0),k3_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_320,c_0_29]),c_0_56]),c_0_25]),c_0_26])]),c_0_38]),c_0_27]),
    [final]).

cnf(c_0_463,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_67]),
    [final]).

cnf(c_0_464,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk4_0)) = k5_tmap_1(esk2_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321,c_0_29]),c_0_25]),c_0_26])]),c_0_27]),c_0_38]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.47  #
% 0.21/0.47  # Preprocessing time       : 0.029 s
% 0.21/0.47  # Presaturation interreduction done
% 0.21/0.47  
% 0.21/0.47  # No proof found!
% 0.21/0.47  # SZS status CounterSatisfiable
% 0.21/0.47  # SZS output start Saturation
% 0.21/0.47  fof(t118_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tsep_1(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_tmap_1)).
% 0.21/0.47  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.21/0.47  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.21/0.47  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.21/0.47  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.47  fof(t109_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_xboole_0(u1_struct_0(X3),X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 0.21/0.47  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.21/0.47  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.21/0.47  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.47  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.21/0.47  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.47  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.21/0.47  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.21/0.47  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.47  fof(t117_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_tmap_1)).
% 0.21/0.47  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tsep_1(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4))))))), inference(assume_negation,[status(cth)],[t118_tmap_1])).
% 0.21/0.47  fof(c_0_16, plain, ![X19, X20, X21, X22]:((X21!=k8_tmap_1(X19,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|(X22!=u1_struct_0(X20)|X21=k6_tmap_1(X19,X22)))|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk1_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X19)))|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((esk1_3(X19,X20,X21)=u1_struct_0(X20)|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(X21!=k6_tmap_1(X19,esk1_3(X19,X20,X21))|X21=k8_tmap_1(X19,X20)|(~v1_pre_topc(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|~m1_pre_topc(X20,X19)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.21/0.47  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(r1_tsep_1(esk3_0,esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.21/0.47  fof(c_0_18, plain, ![X26, X27]:(((v1_pre_topc(k8_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26)))&(v2_pre_topc(k8_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26))))&(l1_pre_topc(k8_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.21/0.47  fof(c_0_19, plain, ![X17, X18]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k7_tmap_1(X17,X18)=k6_partfun1(u1_struct_0(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.21/0.47  fof(c_0_20, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_pre_topc(X42,X41)|m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.47  fof(c_0_21, plain, ![X32, X33, X34, X35]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32)|(~r1_xboole_0(u1_struct_0(X34),X33)|(~m1_subset_1(X35,u1_struct_0(X34))|r1_tmap_1(X34,k6_tmap_1(X32,X33),k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).
% 0.21/0.47  fof(c_0_22, plain, ![X36, X37, X38]:((u1_struct_0(k8_tmap_1(X36,X37))=u1_struct_0(X36)|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(X38!=u1_struct_0(X37)|u1_pre_topc(k8_tmap_1(X36,X37))=k5_tmap_1(X36,X38))|(v2_struct_0(X37)|~m1_pre_topc(X37,X36))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.21/0.47  cnf(c_0_23, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.21/0.47  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_28, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.21/0.47  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_30, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.21/0.47  cnf(c_0_31, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.21/0.47  cnf(c_0_32, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.21/0.47  cnf(c_0_33, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.21/0.47  cnf(c_0_34, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.21/0.47  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X3)|r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~r1_xboole_0(u1_struct_0(X3),X2)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.21/0.47  fof(c_0_36, plain, ![X24, X25]:((~r1_tsep_1(X24,X25)|r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|~l1_struct_0(X25)|~l1_struct_0(X24))&(~r1_xboole_0(u1_struct_0(X24),u1_struct_0(X25))|r1_tsep_1(X24,X25)|~l1_struct_0(X25)|~l1_struct_0(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.21/0.47  cnf(c_0_37, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.21/0.47  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_39, negated_conjecture, (X1=k8_tmap_1(esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_40, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_41, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_42, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_43, negated_conjecture, (esk1_3(esk2_0,esk3_0,X1)=u1_struct_0(esk3_0)|X1=k8_tmap_1(esk2_0,esk3_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_44, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.47  cnf(c_0_45, negated_conjecture, (X1=k8_tmap_1(esk2_0,esk4_0)|m1_subset_1(esk1_3(esk2_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_46, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_47, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_48, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_49, negated_conjecture, (esk1_3(esk2_0,esk4_0,X1)=u1_struct_0(esk4_0)|X1=k8_tmap_1(esk2_0,esk4_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_50, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34]), ['final']).
% 0.21/0.47  cnf(c_0_51, plain, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X3)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X3)),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X3))|~v2_pre_topc(X2)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_35, c_0_34]), ['final']).
% 0.21/0.47  cnf(c_0_52, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.21/0.47  fof(c_0_53, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.47  fof(c_0_54, plain, ![X30, X31]:(~l1_struct_0(X30)|~l1_struct_0(X31)|(~r1_tsep_1(X30,X31)|r1_tsep_1(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.21/0.47  cnf(c_0_55, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.21/0.47  cnf(c_0_56, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk4_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_25]), c_0_26])]), c_0_38]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_57, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_58, negated_conjecture, (esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))=u1_struct_0(esk3_0)|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_41]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_59, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])]), c_0_31]), c_0_34]), c_0_30]), c_0_28]), ['final']).
% 0.21/0.47  cnf(c_0_60, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_61, negated_conjecture, (esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk4_0)|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_47]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_62, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_29]), c_0_25]), c_0_26])]), c_0_27])).
% 0.21/0.47  cnf(c_0_63, plain, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X3)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X3)),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X3,X2)|~l1_struct_0(X3)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_51, c_0_52]), ['final']).
% 0.21/0.47  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  fof(c_0_65, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.47  cnf(c_0_66, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53]), ['final']).
% 0.21/0.47  cnf(c_0_67, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_68, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54]), ['final']).
% 0.21/0.47  cnf(c_0_69, negated_conjecture, (r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_70, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58]), ['final']).
% 0.21/0.47  cnf(c_0_71, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=k8_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_72, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61]), ['final']).
% 0.21/0.47  cnf(c_0_73, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk4_0))=k8_tmap_1(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_74, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk4_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_62]), ['final']).
% 0.21/0.47  cnf(c_0_75, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,X2)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk4_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_38])).
% 0.21/0.47  cnf(c_0_76, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 0.21/0.47  cnf(c_0_77, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_29]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_78, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_24]), c_0_25]), c_0_26])]), c_0_67]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_79, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_80, negated_conjecture, (r1_tsep_1(X1,k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_81, negated_conjecture, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~r1_tsep_1(X1,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_82, negated_conjecture, (r1_tsep_1(X1,k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69]), ['final']).
% 0.21/0.47  cnf(c_0_83, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_70]), c_0_71]), c_0_71]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_84, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_72]), c_0_73]), c_0_73]), c_0_25]), c_0_26])]), c_0_27]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,X2)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_86, negated_conjecture, (r1_tsep_1(X1,k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_87, negated_conjecture, (r1_tsep_1(esk4_0,esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_79]), ['final']).
% 0.21/0.47  cnf(c_0_88, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_89, negated_conjecture, (r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_80]), ['final']).
% 0.21/0.47  cnf(c_0_90, negated_conjecture, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.21/0.47  cnf(c_0_91, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_83, c_0_52])).
% 0.21/0.47  cnf(c_0_92, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_24]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_93, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_84, c_0_52])).
% 0.21/0.47  cnf(c_0_94, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_78]), c_0_78]), c_0_78])).
% 0.21/0.47  cnf(c_0_95, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_80]), c_0_56]), c_0_56]), c_0_56])).
% 0.21/0.47  cnf(c_0_96, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_85, c_0_87])).
% 0.21/0.47  cnf(c_0_97, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_78]), c_0_47]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_98, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.21/0.47  cnf(c_0_99, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),X2),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),X2),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),X2),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_56]), c_0_41]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_100, negated_conjecture, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_101, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_102, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_103, negated_conjecture, (r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_104, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_105, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_106, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_107, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_56]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_108, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_78]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_109, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_70]), ['final']).
% 0.21/0.47  cnf(c_0_110, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_111, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_72]), ['final']).
% 0.21/0.47  cnf(c_0_112, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_70]), ['final']).
% 0.21/0.47  cnf(c_0_113, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_72]), ['final']).
% 0.21/0.47  cnf(c_0_114, negated_conjecture, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~r1_tsep_1(esk2_0,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_100, c_0_52]), ['final']).
% 0.21/0.47  cnf(c_0_115, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_116, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_78])).
% 0.21/0.47  cnf(c_0_117, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_118, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_101, c_0_56])).
% 0.21/0.47  cnf(c_0_119, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_102, c_0_78])).
% 0.21/0.47  cnf(c_0_120, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_102, c_0_56])).
% 0.21/0.47  fof(c_0_121, plain, ![X11, X12, X13, X14, X15, X16]:((~r1_funct_2(X11,X12,X13,X14,X15,X16)|X15=X16|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(X15!=X16|r1_funct_2(X11,X12,X13,X14,X15,X16)|(v1_xboole_0(X12)|v1_xboole_0(X14)|~v1_funct_1(X15)|~v1_funct_2(X15,X11,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.21/0.47  fof(c_0_122, plain, ![X28, X29]:(((v1_funct_1(k9_tmap_1(X28,X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28)))&(v1_funct_2(k9_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28))))&(m1_subset_1(k9_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.21/0.47  cnf(c_0_123, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_63, c_0_78])).
% 0.21/0.47  cnf(c_0_124, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_63, c_0_56])).
% 0.21/0.47  cnf(c_0_125, negated_conjecture, (r1_tsep_1(X1,k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_103]), ['final']).
% 0.21/0.47  cnf(c_0_126, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_127, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_128, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_129, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_107]), c_0_25]), c_0_26])]), c_0_27])).
% 0.21/0.47  cnf(c_0_130, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_108]), c_0_25]), c_0_26])]), c_0_27])).
% 0.21/0.47  cnf(c_0_131, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_109, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_132, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~r1_tsep_1(X1,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_110, c_0_52]), ['final']).
% 0.21/0.47  cnf(c_0_133, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_111, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_134, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_112, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_135, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_113, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_136, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_109, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_137, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk2_0,X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_51, c_0_114])).
% 0.21/0.47  cnf(c_0_138, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_111, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_139, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_112, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_140, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_113, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_141, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_35, c_0_115]), ['final']).
% 0.21/0.47  cnf(c_0_142, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_143, negated_conjecture, (r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_86]), ['final']).
% 0.21/0.47  cnf(c_0_144, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_35, c_0_117]), ['final']).
% 0.21/0.47  cnf(c_0_145, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_146, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_147, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_148, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_149, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_150, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_151, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.21/0.47  cnf(c_0_152, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_122]), ['final']).
% 0.21/0.47  cnf(c_0_153, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_122]), ['final']).
% 0.21/0.47  cnf(c_0_154, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_122]), ['final']).
% 0.21/0.47  cnf(c_0_155, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_156, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),X1)=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_56]), c_0_41]), c_0_42])])).
% 0.21/0.47  cnf(c_0_157, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_78]), c_0_47]), c_0_48])])).
% 0.21/0.47  fof(c_0_158, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.47  cnf(c_0_159, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_160, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(k8_tmap_1(esk2_0,esk4_0),X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_161, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_125]), c_0_78]), c_0_78]), c_0_78])).
% 0.21/0.47  cnf(c_0_162, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_126, c_0_114])).
% 0.21/0.47  cnf(c_0_163, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_126, c_0_52])).
% 0.21/0.47  cnf(c_0_164, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_82]), c_0_56]), c_0_56]), c_0_56])).
% 0.21/0.47  cnf(c_0_165, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_127, c_0_114])).
% 0.21/0.47  cnf(c_0_166, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_127, c_0_52])).
% 0.21/0.47  cnf(c_0_167, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_29]), c_0_71]), c_0_71]), c_0_25]), c_0_24]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_168, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_169, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_170, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.21/0.47  cnf(c_0_171, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_131, c_0_52])).
% 0.21/0.47  cnf(c_0_172, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_133, c_0_132])).
% 0.21/0.47  cnf(c_0_173, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_133, c_0_52])).
% 0.21/0.47  cnf(c_0_174, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_134, c_0_132])).
% 0.21/0.47  cnf(c_0_175, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_134, c_0_52])).
% 0.21/0.47  cnf(c_0_176, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_135, c_0_132])).
% 0.21/0.47  cnf(c_0_177, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_135, c_0_52])).
% 0.21/0.47  cnf(c_0_178, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_136, c_0_132])).
% 0.21/0.47  cnf(c_0_179, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_180, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_136, c_0_52])).
% 0.21/0.47  cnf(c_0_181, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_138, c_0_132])).
% 0.21/0.47  cnf(c_0_182, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_138, c_0_52])).
% 0.21/0.47  cnf(c_0_183, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_139, c_0_132])).
% 0.21/0.47  cnf(c_0_184, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_139, c_0_52])).
% 0.21/0.47  cnf(c_0_185, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_140, c_0_132])).
% 0.21/0.47  cnf(c_0_186, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X2))|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_187, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_188, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X2))|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_189, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_190, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_140, c_0_52])).
% 0.21/0.47  cnf(c_0_191, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_192, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_193, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_141, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_194, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_142, c_0_143])).
% 0.21/0.47  cnf(c_0_195, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_144, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_196, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_145, c_0_89])).
% 0.21/0.47  cnf(c_0_197, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_146, c_0_143])).
% 0.21/0.47  cnf(c_0_198, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_147, c_0_89])).
% 0.21/0.47  cnf(c_0_199, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_148, c_0_132])).
% 0.21/0.47  cnf(c_0_200, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_148, c_0_52])).
% 0.21/0.47  cnf(c_0_201, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_149, c_0_132])).
% 0.21/0.47  cnf(c_0_202, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk3_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_149, c_0_52])).
% 0.21/0.47  cnf(c_0_203, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_150, c_0_132])).
% 0.21/0.47  cnf(c_0_204, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_150, c_0_52])).
% 0.21/0.47  cnf(c_0_205, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_206, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~r1_tsep_1(esk2_0,esk2_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_100, c_0_114]), ['final']).
% 0.21/0.47  cnf(c_0_207, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)), inference(er,[status(thm)],[c_0_151]), ['final']).
% 0.21/0.47  cnf(c_0_208, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_24]), c_0_78]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_209, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_24]), c_0_78]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_210, negated_conjecture, (v1_funct_1(k9_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_211, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_155, c_0_132])).
% 0.21/0.47  cnf(c_0_212, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_29]), c_0_56]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_213, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_29]), c_0_56]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_214, negated_conjecture, (v1_funct_1(k9_tmap_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_215, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_155, c_0_52])).
% 0.21/0.47  cnf(c_0_216, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_217, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_34]), c_0_26])])).
% 0.21/0.47  cnf(c_0_218, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_34]), c_0_26])])).
% 0.21/0.47  cnf(c_0_219, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_158]), ['final']).
% 0.21/0.47  fof(c_0_220, plain, ![X39, X40]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~m1_pre_topc(X40,X39)|r1_funct_2(u1_struct_0(X39),u1_struct_0(k8_tmap_1(X39,X40)),u1_struct_0(X39),u1_struct_0(X39),k9_tmap_1(X39,X40),k3_struct_0(X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_tmap_1])])])])).
% 0.21/0.47  cnf(c_0_221, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.47  cnf(c_0_222, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_159, c_0_143])).
% 0.21/0.47  cnf(c_0_223, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_160, c_0_89])).
% 0.21/0.47  cnf(c_0_224, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_225, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_226, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_227, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_228, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_229, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_230, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_57]), ['final']).
% 0.21/0.47  cnf(c_0_231, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(X1)),esk4_0),esk5_0)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_167, c_0_168]), ['final']).
% 0.21/0.47  cnf(c_0_232, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_60]), ['final']).
% 0.21/0.47  cnf(c_0_233, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(X1)),esk4_0),esk5_0)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_167, c_0_169]), ['final']).
% 0.21/0.47  cnf(c_0_234, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_57]), ['final']).
% 0.21/0.47  cnf(c_0_235, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_60]), ['final']).
% 0.21/0.47  cnf(c_0_236, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_57]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_237, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_238, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_239, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_240, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_241, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_109, c_0_52])).
% 0.21/0.47  cnf(c_0_242, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),X1),X2)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_60]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_243, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_244, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_111, c_0_52])).
% 0.21/0.47  cnf(c_0_245, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_112, c_0_52])).
% 0.21/0.47  cnf(c_0_246, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_113, c_0_52])).
% 0.21/0.47  cnf(c_0_247, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_248, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_249, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_250, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_251, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_179, c_0_78])).
% 0.21/0.47  cnf(c_0_252, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_253, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_254, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk4_0))|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_179, c_0_56])).
% 0.21/0.47  cnf(c_0_255, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_256, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_257, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_184, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_258, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_259, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X2,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_186, c_0_132])).
% 0.21/0.47  cnf(c_0_260, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_187, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_261, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_186, c_0_52])).
% 0.21/0.47  cnf(c_0_262, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X2,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_188, c_0_132])).
% 0.21/0.47  cnf(c_0_263, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_264, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_188, c_0_52])).
% 0.21/0.47  cnf(c_0_265, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_190, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_266, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_267, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_268, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_struct_0(esk2_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_193, c_0_52])).
% 0.21/0.47  cnf(c_0_269, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_270, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~l1_struct_0(esk2_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_195, c_0_52])).
% 0.21/0.47  cnf(c_0_271, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_196, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_272, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk2_0,X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_141, c_0_114])).
% 0.21/0.47  cnf(c_0_273, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_274, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,esk2_0)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_141, c_0_52])).
% 0.21/0.47  cnf(c_0_275, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(esk2_0,X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_144, c_0_114])).
% 0.21/0.47  cnf(c_0_276, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_277, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X1,esk2_0)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(esk2_0)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_144, c_0_52])).
% 0.21/0.47  cnf(c_0_278, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_279, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_280, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_struct_0(esk4_0)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_64]), c_0_38])).
% 0.21/0.47  cnf(c_0_281, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_201, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_282, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_202, c_0_76]), c_0_92])])).
% 0.21/0.47  cnf(c_0_283, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk4_0),esk5_0)|~r1_tsep_1(esk4_0,esk4_0)|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_64]), c_0_29])]), c_0_38])).
% 0.21/0.47  cnf(c_0_284, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_285, negated_conjecture, (r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk2_0),X3)|v2_struct_0(X1)|~r1_tsep_1(X2,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk2_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_132]), c_0_27])).
% 0.21/0.47  cnf(c_0_286, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_204, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_287, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,esk2_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_205, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_288, negated_conjecture, (r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk2_0),X2)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,X1)|~l1_struct_0(esk2_0)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_206]), c_0_27])).
% 0.21/0.47  cnf(c_0_289, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k9_tmap_1(esk2_0,esk3_0),X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207, c_0_208]), c_0_209]), c_0_210])]), ['final']).
% 0.21/0.47  cnf(c_0_290, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_291, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk4_0),k9_tmap_1(esk2_0,esk4_0))|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~m1_subset_1(k9_tmap_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k9_tmap_1(esk2_0,esk4_0),X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207, c_0_212]), c_0_213]), c_0_214])]), ['final']).
% 0.21/0.47  cnf(c_0_292, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215, c_0_76]), c_0_77])])).
% 0.21/0.47  cnf(c_0_293, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,esk2_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_216, c_0_76]), c_0_26])])).
% 0.21/0.47  cnf(c_0_294, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(X2))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_169, c_0_168]), ['final']).
% 0.21/0.47  cnf(c_0_295, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_296, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(X2))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_169, c_0_169]), ['final']).
% 0.21/0.47  cnf(c_0_297, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_121]), ['final']).
% 0.21/0.47  cnf(c_0_298, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_157, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_299, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_156, c_0_107])).
% 0.21/0.47  cnf(c_0_300, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_156, c_0_108])).
% 0.21/0.47  cnf(c_0_301, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_157, c_0_107])).
% 0.21/0.47  cnf(c_0_302, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_157, c_0_108])).
% 0.21/0.47  cnf(c_0_303, negated_conjecture, (k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))=k6_partfun1(u1_struct_0(esk2_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_60]), c_0_25]), c_0_26])]), c_0_27])).
% 0.21/0.47  cnf(c_0_304, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_217, c_0_29])).
% 0.21/0.47  cnf(c_0_305, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_217, c_0_24])).
% 0.21/0.47  cnf(c_0_306, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_218, c_0_29])).
% 0.21/0.47  cnf(c_0_307, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_115]), c_0_26])])).
% 0.21/0.47  cnf(c_0_308, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_218, c_0_24])).
% 0.21/0.47  cnf(c_0_309, negated_conjecture, (k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))=k6_partfun1(u1_struct_0(esk2_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_57]), c_0_25]), c_0_26])]), c_0_27])).
% 0.21/0.47  cnf(c_0_310, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_117]), c_0_26])])).
% 0.21/0.47  cnf(c_0_311, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_115]), c_0_26])])).
% 0.21/0.47  cnf(c_0_312, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_117]), c_0_26])])).
% 0.21/0.47  cnf(c_0_313, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_129, c_0_56])).
% 0.21/0.47  cnf(c_0_314, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_129, c_0_78])).
% 0.21/0.47  cnf(c_0_315, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_130, c_0_56])).
% 0.21/0.47  cnf(c_0_316, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_130, c_0_78])).
% 0.21/0.47  cnf(c_0_317, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(X2))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_129, c_0_129]), ['final']).
% 0.21/0.47  cnf(c_0_318, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_219, c_0_78])).
% 0.21/0.47  cnf(c_0_319, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_219, c_0_56])).
% 0.21/0.47  cnf(c_0_320, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_220]), ['final']).
% 0.21/0.47  cnf(c_0_321, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_221]), c_0_34]), ['final']).
% 0.21/0.47  cnf(c_0_322, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_222, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_323, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X2),u1_struct_0(esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_223, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_324, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_224, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_325, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_225, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_326, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_226, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_327, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(esk4_0))|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_227, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_328, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_329, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk4_0,esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_229, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_330, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_230, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_331, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_231, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_332, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_231, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_333, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_232, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_334, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_233, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_335, negated_conjecture, (r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)),esk4_0),esk5_0)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_233, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_336, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_234, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_337, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_235, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_338, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_230, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_339, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_232, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_340, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_234, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_341, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_235, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_342, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_236, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_343, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_237, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_344, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0))),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_236, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_345, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_238, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_346, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_347, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_240, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_348, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_241, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_349, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_242, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_350, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_351, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_244, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_352, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_353, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_246, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_354, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0))),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk2_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_242, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_355, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_247, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_356, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_248, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_357, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_108]), ['final']).
% 0.21/0.47  cnf(c_0_358, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_249, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_359, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_250, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_360, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_361, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_97, c_0_107]), ['final']).
% 0.21/0.47  cnf(c_0_362, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_252, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_363, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_253, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_364, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,k8_tmap_1(esk2_0,esk4_0))|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_254, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_365, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X2)),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X2,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_34]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_366, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_255, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_367, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_256, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_368, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_115]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_369, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_257, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_370, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_258, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_371, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(X2,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_259, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_372, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_117]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_373, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_260, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_374, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk3_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_261, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_375, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(X2,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_262, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_376, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_263, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_377, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),k8_tmap_1(esk2_0,esk4_0)),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_264, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_378, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_265, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_379, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_266, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_380, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0)),esk2_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_267, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_381, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_268, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_382, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_269, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_383, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk4_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_270, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_384, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_99, c_0_108]), ['final']).
% 0.21/0.47  cnf(c_0_385, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_271, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_386, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_272, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_387, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_107]), ['final']).
% 0.21/0.47  cnf(c_0_388, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_273, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_389, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_274, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_390, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_275, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_391, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X2)),X1),X3)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X2,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_34]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_392, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_xboole_0(u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_276, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_393, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(esk2_0)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(esk2_0)),k7_tmap_1(X2,u1_struct_0(esk2_0)),X1),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X1,esk2_0)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X2)|~m1_pre_topc(X1,X2)|~l1_struct_0(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_277, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_394, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_115]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_395, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_278, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_396, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_279, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_397, negated_conjecture, (r1_tmap_1(esk4_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk4_0),esk5_0)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk4_0)|~v2_pre_topc(X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_280, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_398, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k2_tmap_1(k8_tmap_1(esk2_0,esk4_0),k6_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0)),X1),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_117]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_399, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_281, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_400, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_282, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_401, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk4_0),esk5_0)|~r1_tsep_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_283, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_402, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_284, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_403, negated_conjecture, (r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(X2)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X2)),k7_tmap_1(X1,u1_struct_0(X2)),esk2_0),X3)|v2_struct_0(X1)|~r1_tsep_1(X2,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_285, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_404, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(esk2_0,u1_struct_0(X2)),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,u1_struct_0(X2)),k7_tmap_1(esk2_0,u1_struct_0(X2)),X1),X3)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_108]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_405, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(esk2_0,u1_struct_0(X2)),k2_tmap_1(esk2_0,k6_tmap_1(esk2_0,u1_struct_0(X2)),k7_tmap_1(esk2_0,u1_struct_0(X2)),X1),X3)|v2_struct_0(X1)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_107]), c_0_25]), c_0_26])]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_406, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk3_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_407, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)|~r1_tsep_1(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_287, c_0_76]), c_0_92])]), ['final']).
% 0.21/0.47  cnf(c_0_408, negated_conjecture, (r1_tmap_1(esk2_0,k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),esk2_0),X2)|v2_struct_0(X1)|~r1_tsep_1(esk2_0,esk2_0)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_288, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_409, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289, c_0_208]), c_0_209])]), ['final']).
% 0.21/0.47  cnf(c_0_410, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_290, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_411, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk4_0),k9_tmap_1(esk2_0,esk4_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_291, c_0_212]), c_0_213])]), ['final']).
% 0.21/0.47  cnf(c_0_412, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k8_tmap_1(esk2_0,esk4_0)),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~r1_tsep_1(esk2_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_292, c_0_76]), c_0_26])]), ['final']).
% 0.21/0.47  cnf(c_0_413, negated_conjecture, (k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|r1_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk4_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk2_0),X1)|~r1_tsep_1(esk4_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_293, c_0_76]), c_0_77])]), ['final']).
% 0.21/0.47  cnf(c_0_414, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_294, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_415, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(X1))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_294, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_416, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_294, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_417, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_294, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_418, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_295, c_0_57]), ['final']).
% 0.21/0.47  cnf(c_0_419, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_296, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_420, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_296, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_421, negated_conjecture, (X1=k9_tmap_1(esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k9_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297, c_0_208]), c_0_209]), c_0_210])]), ['final']).
% 0.21/0.47  cnf(c_0_422, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_295, c_0_60]), ['final']).
% 0.21/0.47  cnf(c_0_423, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_298, c_0_57]), ['final']).
% 0.21/0.47  cnf(c_0_424, negated_conjecture, (X1=k9_tmap_1(esk2_0,esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k9_tmap_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_297, c_0_212]), c_0_213]), c_0_214])]), ['final']).
% 0.21/0.47  cnf(c_0_425, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_298, c_0_60]), ['final']).
% 0.21/0.47  cnf(c_0_426, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_299, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_427, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_300, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_428, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_301, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_429, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_302, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_430, negated_conjecture, (k7_tmap_1(esk2_0,esk1_3(esk2_0,esk4_0,k8_tmap_1(esk2_0,esk3_0)))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_303, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_431, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk4_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_304, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_432, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_305, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_433, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk4_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_306, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_434, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_307, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_435, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_217, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_436, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_218, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_437, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_308, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_438, negated_conjecture, (k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,k8_tmap_1(esk2_0,esk4_0)))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|k8_tmap_1(esk2_0,esk4_0)=k8_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_309, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_439, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk4_0),u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_310, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_440, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_311, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_441, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_312, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_442, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_313, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_443, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_314, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_444, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_315, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_445, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_316, c_0_62]), c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_446, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_317, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_447, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_317, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_448, negated_conjecture, (k6_partfun1(u1_struct_0(X1))=k7_tmap_1(X1,u1_struct_0(esk2_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_115]), ['final']).
% 0.21/0.47  cnf(c_0_449, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk1_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.21/0.47  cnf(c_0_450, negated_conjecture, (k6_partfun1(u1_struct_0(X1))=k7_tmap_1(X1,u1_struct_0(esk2_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_117]), ['final']).
% 0.21/0.47  cnf(c_0_451, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_108, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_452, negated_conjecture, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk2_0))|~r1_tsep_1(X1,k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_453, negated_conjecture, (r1_xboole_0(u1_struct_0(esk2_0),u1_struct_0(X1))|~r1_tsep_1(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_struct_0(k8_tmap_1(esk2_0,esk3_0))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_454, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_108, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_455, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_107, c_0_78]), ['final']).
% 0.21/0.47  cnf(c_0_456, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk4_0),k8_tmap_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_107, c_0_56]), ['final']).
% 0.21/0.47  cnf(c_0_457, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_318, c_0_76]), c_0_48])]), ['final']).
% 0.21/0.47  cnf(c_0_458, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk4_0))|~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_319, c_0_76]), c_0_42])]), ['final']).
% 0.21/0.47  cnf(c_0_459, negated_conjecture, (~r1_tmap_1(esk4_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.21/0.47  cnf(c_0_460, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_62, c_0_74]), ['final']).
% 0.21/0.47  cnf(c_0_461, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_320, c_0_24]), c_0_78]), c_0_25]), c_0_26])]), c_0_67]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_462, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk4_0),k3_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_320, c_0_29]), c_0_56]), c_0_25]), c_0_26])]), c_0_38]), c_0_27]), ['final']).
% 0.21/0.47  cnf(c_0_463, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_67]), ['final']).
% 0.21/0.47  cnf(c_0_464, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk4_0))=k5_tmap_1(esk2_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_321, c_0_29]), c_0_25]), c_0_26])]), c_0_27]), c_0_38]), ['final']).
% 0.21/0.47  # SZS output end Saturation
% 0.21/0.47  # Proof object total steps             : 465
% 0.21/0.47  # Proof object clause steps            : 434
% 0.21/0.47  # Proof object formula steps           : 31
% 0.21/0.47  # Proof object conjectures             : 407
% 0.21/0.47  # Proof object clause conjectures      : 404
% 0.21/0.47  # Proof object formula conjectures     : 3
% 0.21/0.47  # Proof object initial clauses used    : 34
% 0.21/0.47  # Proof object initial formulas used   : 15
% 0.21/0.47  # Proof object generating inferences   : 372
% 0.21/0.47  # Proof object simplifying inferences  : 568
% 0.21/0.47  # Parsed axioms                        : 15
% 0.21/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.47  # Initial clauses                      : 34
% 0.21/0.47  # Removed in clause preprocessing      : 0
% 0.21/0.47  # Initial clauses in saturation        : 34
% 0.21/0.47  # Processed clauses                    : 729
% 0.21/0.47  # ...of these trivial                  : 0
% 0.21/0.47  # ...subsumed                          : 248
% 0.21/0.47  # ...remaining for further processing  : 481
% 0.21/0.47  # Other redundant clauses eliminated   : 4
% 0.21/0.47  # Clauses deleted for lack of memory   : 0
% 0.21/0.47  # Backward-subsumed                    : 133
% 0.21/0.47  # Backward-rewritten                   : 27
% 0.21/0.47  # Generated clauses                    : 682
% 0.21/0.47  # ...of the previous two non-trivial   : 671
% 0.21/0.47  # Contextual simplify-reflections      : 5
% 0.21/0.47  # Paramodulations                      : 679
% 0.21/0.47  # Factorizations                       : 0
% 0.21/0.47  # Equation resolutions                 : 4
% 0.21/0.47  # Propositional unsat checks           : 0
% 0.21/0.47  #    Propositional check models        : 0
% 0.21/0.47  #    Propositional check unsatisfiable : 0
% 0.21/0.47  #    Propositional clauses             : 0
% 0.21/0.47  #    Propositional clauses after purity: 0
% 0.21/0.47  #    Propositional unsat core size     : 0
% 0.21/0.47  #    Propositional preprocessing time  : 0.000
% 0.21/0.47  #    Propositional encoding time       : 0.000
% 0.21/0.47  #    Propositional solver time         : 0.000
% 0.21/0.47  #    Success case prop preproc time    : 0.000
% 0.21/0.47  #    Success case prop encoding time   : 0.000
% 0.21/0.47  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 284
% 0.21/0.48  #    Positive orientable unit clauses  : 31
% 0.21/0.48  #    Positive unorientable unit clauses: 0
% 0.21/0.48  #    Negative unit clauses             : 4
% 0.21/0.48  #    Non-unit-clauses                  : 249
% 0.21/0.48  # Current number of unprocessed clauses: 0
% 0.21/0.48  # ...number of literals in the above   : 0
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 194
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 68220
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 1577
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 382
% 0.21/0.48  # Unit Clause-clause subsumption calls : 372
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 7
% 0.21/0.48  # BW rewrite match successes           : 4
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 43285
% 0.21/0.48  
% 0.21/0.48  # -------------------------------------------------
% 0.21/0.48  # User time                : 0.127 s
% 0.21/0.48  # System time              : 0.004 s
% 0.21/0.48  # Total time               : 0.131 s
% 0.21/0.48  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
