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
% DateTime   : Thu Dec  3 11:18:25 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   92 (1831 expanded)
%              Number of clauses        :   73 ( 582 expanded)
%              Number of leaves         :    9 ( 455 expanded)
%              Depth                    :    9
%              Number of atoms          :  482 (9625 expanded)
%              Number of equality atoms :   82 ( 473 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_tmap_1)).

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

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_tmap_1])).

fof(c_0_10,plain,(
    ! [X22,X23,X24] :
      ( ( u1_struct_0(k8_tmap_1(X22,X23)) = u1_struct_0(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | X24 != u1_struct_0(X23)
        | u1_pre_topc(k8_tmap_1(X22,X23)) = k5_tmap_1(X22,X24)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k3_struct_0(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ( v1_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( v2_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( l1_pre_topc(k8_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_13,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X10 != k8_tmap_1(X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | X11 != u1_struct_0(X9)
        | X10 = k6_tmap_1(X8,X11)
        | ~ v1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))
        | X10 = k8_tmap_1(X8,X9)
        | ~ v1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( esk1_3(X8,X9,X10) = u1_struct_0(X9)
        | X10 = k8_tmap_1(X8,X9)
        | ~ v1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( X10 != k6_tmap_1(X8,esk1_3(X8,X9,X10))
        | X10 = k8_tmap_1(X8,X9)
        | ~ v1_pre_topc(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_14,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_15,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_21,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | k7_tmap_1(X6,X7) = k6_partfun1(u1_struct_0(X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_23,plain,(
    ! [X13,X14,X15,X16] :
      ( ( X15 != k9_tmap_1(X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | X16 != u1_struct_0(X14)
        | r1_funct_2(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)),u1_struct_0(X13),u1_struct_0(k6_tmap_1(X13,X16)),X15,k7_tmap_1(X13,X16))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))))
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))
        | X15 = k9_tmap_1(X13,X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))))
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( esk2_3(X13,X14,X15) = u1_struct_0(X14)
        | X15 = k9_tmap_1(X13,X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))))
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r1_funct_2(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)),u1_struct_0(X13),u1_struct_0(k6_tmap_1(X13,esk2_3(X13,X14,X15))),X15,k7_tmap_1(X13,esk2_3(X13,X14,X15)))
        | X15 = k9_tmap_1(X13,X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))))
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ( v1_funct_1(k9_tmap_1(X20,X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) )
      & ( v1_funct_2(k9_tmap_1(X20,X21),u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) )
      & ( m1_subset_1(k9_tmap_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_pre_topc(X21,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_27,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_28,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_34,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_35,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_36,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])]),c_0_21]),c_0_26]),c_0_27]),c_0_28]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_29]),c_0_30])]),
    [final]).

cnf(c_0_38,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_40,plain,
    ( r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])]),c_0_27]),c_0_33]),c_0_34]),c_0_35]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_37]),c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk3_0)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1) = k6_partfun1(u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_39]),c_0_30])])).

cnf(c_0_45,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_29]),c_0_41]),c_0_29]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(X1)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_18])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29]),
    [final]).

cnf(c_0_50,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [final]).

cnf(c_0_53,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

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
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_55,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) = k6_partfun1(u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0)) = k6_partfun1(u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) = k6_partfun1(u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_49]),c_0_18])])).

cnf(c_0_60,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk3_0)) = k7_tmap_1(esk3_0,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_47]),c_0_17]),c_0_18])]),c_0_20])).

cnf(c_0_61,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_62,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(X1)) = k7_tmap_1(esk3_0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_42]),
    [final]).

fof(c_0_63,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k3_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_65,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_27]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( X1 = k9_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk3_0,esk4_0),esk2_3(k8_tmap_1(esk3_0,esk4_0),X2,X1))),X1,k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),esk2_3(k8_tmap_1(esk3_0,esk4_0),X2,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_29]),c_0_39]),c_0_30])]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_29]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( X1 = k9_tmap_1(esk3_0,esk4_0)
    | ~ r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk2_3(esk3_0,esk4_0,X1))),X1,k7_tmap_1(esk3_0,esk2_3(esk3_0,esk4_0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_29]),c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( X1 = k9_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)
    | m1_subset_1(esk2_3(k8_tmap_1(esk3_0,esk4_0),X2,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_39]),c_0_30])]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( esk2_3(k8_tmap_1(esk3_0,esk4_0),X1,X2) = u1_struct_0(X1)
    | X2 = k9_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_39]),c_0_30])]),
    [final]).

cnf(c_0_71,negated_conjecture,
    ( X1 = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_72,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,X1) = u1_struct_0(esk4_0)
    | X1 = k9_tmap_1(esk3_0,esk4_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( X1 = k8_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_43]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_43]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_43]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_43]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_43]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0)) = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_43]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k7_tmap_1(esk3_0,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_43]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( esk1_3(esk3_0,esk4_0,X1) = u1_struct_0(esk4_0)
    | X1 = k8_tmap_1(esk3_0,esk4_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(X1)) = k7_tmap_1(esk3_0,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_29]),
    [final]).

cnf(c_0_83,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( k6_partfun1(u1_struct_0(X1)) = k7_tmap_1(X1,u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_49]),
    [final]).

cnf(c_0_85,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k3_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_29]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) = k5_tmap_1(esk3_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),c_0_19]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_29]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_29]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_17]),c_0_18])]),c_0_20]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.031 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # No proof found!
% 0.14/0.39  # SZS status CounterSatisfiable
% 0.14/0.39  # SZS output start Saturation
% 0.14/0.39  fof(t117_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_tmap_1)).
% 0.14/0.39  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.14/0.39  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.14/0.39  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.14/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.14/0.39  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.14/0.39  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.14/0.39  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.14/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))))), inference(assume_negation,[status(cth)],[t117_tmap_1])).
% 0.14/0.39  fof(c_0_10, plain, ![X22, X23, X24]:((u1_struct_0(k8_tmap_1(X22,X23))=u1_struct_0(X22)|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(X24!=u1_struct_0(X23)|u1_pre_topc(k8_tmap_1(X22,X23))=k5_tmap_1(X22,X24))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.14/0.39  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&~r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k3_struct_0(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X18, X19]:(((v1_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))&(v2_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18))))&(l1_pre_topc(k8_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.14/0.39  fof(c_0_13, plain, ![X8, X9, X10, X11]:((X10!=k8_tmap_1(X8,X9)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))|(X11!=u1_struct_0(X9)|X10=k6_tmap_1(X8,X11)))|(~v1_pre_topc(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&((m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))|X10=k8_tmap_1(X8,X9)|(~v1_pre_topc(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&((esk1_3(X8,X9,X10)=u1_struct_0(X9)|X10=k8_tmap_1(X8,X9)|(~v1_pre_topc(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(X10!=k6_tmap_1(X8,esk1_3(X8,X9,X10))|X10=k8_tmap_1(X8,X9)|(~v1_pre_topc(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.14/0.39  fof(c_0_14, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.14/0.39  cnf(c_0_15, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.39  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.39  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.39  cnf(c_0_21, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.39  fof(c_0_22, plain, ![X6, X7]:(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|(~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|k7_tmap_1(X6,X7)=k6_partfun1(u1_struct_0(X6)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.14/0.39  fof(c_0_23, plain, ![X13, X14, X15, X16]:((X15!=k9_tmap_1(X13,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))|(X16!=u1_struct_0(X14)|r1_funct_2(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)),u1_struct_0(X13),u1_struct_0(k6_tmap_1(X13,X16)),X15,k7_tmap_1(X13,X16))))|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14))))))|~m1_pre_topc(X14,X13)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))|X15=k9_tmap_1(X13,X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14))))))|~m1_pre_topc(X14,X13)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&((esk2_3(X13,X14,X15)=u1_struct_0(X14)|X15=k9_tmap_1(X13,X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14))))))|~m1_pre_topc(X14,X13)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(~r1_funct_2(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)),u1_struct_0(X13),u1_struct_0(k6_tmap_1(X13,esk2_3(X13,X14,X15))),X15,k7_tmap_1(X13,esk2_3(X13,X14,X15)))|X15=k9_tmap_1(X13,X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14))))))|~m1_pre_topc(X14,X13)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.14/0.39  fof(c_0_24, plain, ![X20, X21]:(((v1_funct_1(k9_tmap_1(X20,X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_pre_topc(X21,X20)))&(v1_funct_2(k9_tmap_1(X20,X21),u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_pre_topc(X21,X20))))&(m1_subset_1(k9_tmap_1(X20,X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_pre_topc(X21,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.14/0.39  cnf(c_0_25, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_26, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.39  cnf(c_0_27, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.14/0.39  cnf(c_0_28, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (u1_struct_0(k8_tmap_1(esk3_0,esk4_0))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_31, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.14/0.39  cnf(c_0_32, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.39  cnf(c_0_33, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.39  cnf(c_0_34, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.39  cnf(c_0_35, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.39  cnf(c_0_36, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])]), c_0_21]), c_0_26]), c_0_27]), c_0_28]), ['final']).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_29]), c_0_30])]), ['final']).
% 0.14/0.39  cnf(c_0_38, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_27]), ['final']).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_40, plain, (r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])]), c_0_27]), c_0_33]), c_0_34]), c_0_35]), ['final']).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (k6_tmap_1(esk3_0,u1_struct_0(esk4_0))=k8_tmap_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_37]), c_0_17]), c_0_18])]), c_0_20])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (k6_partfun1(u1_struct_0(esk3_0))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)=k6_partfun1(u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_39]), c_0_30])])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_16]), c_0_29]), c_0_41]), c_0_29]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(X1))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_29]), ['final']).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_18])])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_29]), ['final']).
% 0.14/0.39  cnf(c_0_50, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_51, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(X1)))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46]), ['final']).
% 0.14/0.39  cnf(c_0_53, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.14/0.39  cnf(c_0_54, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.14/0.39  cnf(c_0_55, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0))=k6_partfun1(u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0))=k6_partfun1(u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_16])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0))=k6_partfun1(u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_49]), c_0_18])])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (k6_partfun1(u1_struct_0(esk3_0))=k7_tmap_1(esk3_0,u1_struct_0(esk3_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_47]), c_0_17]), c_0_18])]), c_0_20])).
% 0.14/0.39  cnf(c_0_61, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(X1))=k7_tmap_1(esk3_0,u1_struct_0(X2))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_42]), ['final']).
% 0.14/0.39  fof(c_0_63, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.39  cnf(c_0_64, negated_conjecture, (~r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k3_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_65, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]), c_0_27]), ['final']).
% 0.14/0.39  cnf(c_0_66, negated_conjecture, (X1=k9_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk3_0,esk4_0),esk2_3(k8_tmap_1(esk3_0,esk4_0),X2,X1))),X1,k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),esk2_3(k8_tmap_1(esk3_0,esk4_0),X2,X1)))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)))|~v1_funct_1(X1)|~m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_29]), c_0_39]), c_0_30])]), ['final']).
% 0.14/0.39  cnf(c_0_67, negated_conjecture, (r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk3_0)))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_29]), ['final']).
% 0.14/0.39  cnf(c_0_68, negated_conjecture, (X1=k9_tmap_1(esk3_0,esk4_0)|~r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,esk2_3(esk3_0,esk4_0,X1))),X1,k7_tmap_1(esk3_0,esk2_3(esk3_0,esk4_0,X1)))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_29]), c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_69, negated_conjecture, (X1=k9_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)|m1_subset_1(esk2_3(k8_tmap_1(esk3_0,esk4_0),X2,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)))|~v1_funct_1(X1)|~m1_pre_topc(X2,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X2)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_39]), c_0_30])]), ['final']).
% 0.14/0.39  cnf(c_0_70, negated_conjecture, (esk2_3(k8_tmap_1(esk3_0,esk4_0),X1,X2)=u1_struct_0(X1)|X2=k9_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~v1_funct_2(X2,u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)))|~v1_funct_1(X2)|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_29]), c_0_39]), c_0_30])]), ['final']).
% 0.14/0.39  cnf(c_0_71, negated_conjecture, (X1=k9_tmap_1(esk3_0,esk4_0)|m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_72, negated_conjecture, (esk2_3(esk3_0,esk4_0,X1)=u1_struct_0(esk4_0)|X1=k9_tmap_1(esk3_0,esk4_0)|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_29]), c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_73, negated_conjecture, (X1=k8_tmap_1(esk3_0,esk4_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_74, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),X1)=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_44, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_75, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_56, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_76, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_57, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_77, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,esk3_0)), inference(rw,[status(thm)],[c_0_48, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_78, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_58, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_79, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0))=k7_tmap_1(esk3_0,u1_struct_0(esk4_0))|v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),esk3_0)), inference(rw,[status(thm)],[c_0_59, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_80, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(esk4_0))=k7_tmap_1(esk3_0,u1_struct_0(esk3_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_60, c_0_43]), ['final']).
% 0.14/0.39  cnf(c_0_81, negated_conjecture, (esk1_3(esk3_0,esk4_0,X1)=u1_struct_0(esk4_0)|X1=k8_tmap_1(esk3_0,esk4_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_82, negated_conjecture, (k7_tmap_1(esk3_0,u1_struct_0(X1))=k7_tmap_1(esk3_0,u1_struct_0(esk3_0))|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),k8_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(X1,k8_tmap_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_29]), ['final']).
% 0.14/0.39  cnf(c_0_83, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk1_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.14/0.39  cnf(c_0_84, negated_conjecture, (k6_partfun1(u1_struct_0(X1))=k7_tmap_1(X1,u1_struct_0(esk3_0))|v2_struct_0(X1)|~m1_pre_topc(k8_tmap_1(esk3_0,esk4_0),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_49]), ['final']).
% 0.14/0.39  cnf(c_0_85, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.14/0.39  cnf(c_0_86, negated_conjecture, (~r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k3_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_64, c_0_29]), ['final']).
% 0.14/0.39  cnf(c_0_87, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk3_0,esk4_0))=k5_tmap_1(esk3_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), c_0_19]), ['final']).
% 0.14/0.39  cnf(c_0_88, negated_conjecture, (m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_29]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_89, negated_conjecture, (v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_29]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_90, negated_conjecture, (v1_funct_1(k9_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  cnf(c_0_91, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_17]), c_0_18])]), c_0_20]), ['final']).
% 0.14/0.39  # SZS output end Saturation
% 0.14/0.39  # Proof object total steps             : 92
% 0.14/0.39  # Proof object clause steps            : 73
% 0.14/0.39  # Proof object formula steps           : 19
% 0.14/0.39  # Proof object conjectures             : 53
% 0.14/0.39  # Proof object clause conjectures      : 50
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 25
% 0.14/0.39  # Proof object initial formulas used   : 9
% 0.14/0.39  # Proof object generating inferences   : 36
% 0.14/0.39  # Proof object simplifying inferences  : 123
% 0.14/0.39  # Parsed axioms                        : 9
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 25
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 25
% 0.14/0.39  # Processed clauses                    : 128
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 30
% 0.14/0.39  # ...remaining for further processing  : 98
% 0.14/0.39  # Other redundant clauses eliminated   : 5
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 9
% 0.14/0.39  # Generated clauses                    : 71
% 0.14/0.39  # ...of the previous two non-trivial   : 78
% 0.14/0.39  # Contextual simplify-reflections      : 9
% 0.14/0.39  # Paramodulations                      : 68
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 5
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 61
% 0.14/0.39  #    Positive orientable unit clauses  : 14
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 44
% 0.14/0.39  # Current number of unprocessed clauses: 0
% 0.14/0.39  # ...number of literals in the above   : 0
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 34
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1054
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 146
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 39
% 0.14/0.39  # Unit Clause-clause subsumption calls : 24
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 3
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 5999
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.037 s
% 0.14/0.39  # System time              : 0.007 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
