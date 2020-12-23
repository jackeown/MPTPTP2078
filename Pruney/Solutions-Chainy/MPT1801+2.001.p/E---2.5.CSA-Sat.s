%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 (2583 expanded)
%              Number of clauses        :   80 ( 822 expanded)
%              Number of leaves         :   10 ( 640 expanded)
%              Depth                    :   10
%              Number of atoms          :  437 (13173 expanded)
%              Number of equality atoms :   77 ( 587 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
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

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_tmap_1])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] :
      ( ( u1_struct_0(k8_tmap_1(X20,X21)) = u1_struct_0(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | X22 != u1_struct_0(X21)
        | u1_pre_topc(k8_tmap_1(X20,X21)) = k5_tmap_1(X20,X22)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( v2_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( l1_pre_topc(k8_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_14,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_15,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_16,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_22,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_23,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_24,plain,
    ( u1_pre_topc(k8_tmap_1(X2,X3)) = k5_tmap_1(X2,X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X1 != u1_struct_0(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | k6_tmap_1(X14,X15) = g1_pre_topc(u1_struct_0(X14),k5_tmap_1(X14,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_27,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_31,plain,
    ( u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25]),
    [final]).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | k7_tmap_1(X7,X8) = k6_partfun1(u1_struct_0(X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_33,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X11 != k9_tmap_1(X9,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | X12 != u1_struct_0(X10)
        | r1_funct_2(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)),u1_struct_0(X9),u1_struct_0(k6_tmap_1(X9,X12)),X11,k7_tmap_1(X9,X12))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))))
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X9)))
        | X11 = k9_tmap_1(X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))))
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( esk1_3(X9,X10,X11) = u1_struct_0(X10)
        | X11 = k9_tmap_1(X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))))
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r1_funct_2(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)),u1_struct_0(X9),u1_struct_0(k6_tmap_1(X9,esk1_3(X9,X10,X11))),X11,k7_tmap_1(X9,esk1_3(X9,X10,X11)))
        | X11 = k9_tmap_1(X9,X10)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))))
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( ( v1_funct_1(k9_tmap_1(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( v1_funct_2(k9_tmap_1(X18,X19),u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) )
      & ( m1_subset_1(k9_tmap_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_pre_topc(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_37,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_17]),c_0_18]),c_0_19])]),c_0_21]),c_0_20]),
    [final]).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_39,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_42,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_43,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_44,plain,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X2))) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_25]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(esk3_0))) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_30])]),
    [final]).

cnf(c_0_47,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_49,plain,
    ( r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])]),c_0_25]),c_0_41]),c_0_42]),c_0_43]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_45]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_18]),c_0_19])]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_48]),c_0_30])])).

cnf(c_0_54,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_17]),c_0_28]),c_0_50]),c_0_28]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_19])])).

cnf(c_0_59,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)) = k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_48]),c_0_30])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [final]).

cnf(c_0_61,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_62,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_63,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_57]),c_0_19])])).

cnf(c_0_67,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_56]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))) = k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_25]),c_0_19])]),
    [final]).

fof(c_0_70,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_72,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_28]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( X1 = k9_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),X2,X1))),X1,k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),X2,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_28]),c_0_48]),c_0_30])]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( X1 = k9_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X2,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_48]),c_0_30])]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,X2) = u1_struct_0(X1)
    | X2 = k9_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_28]),c_0_48]),c_0_30])]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( X1 = k9_tmap_1(esk2_0,esk3_0)
    | ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,X1))),X1,k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_28]),c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( X1 = k9_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_28]),c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( esk1_3(esk2_0,esk3_0,X1) = u1_struct_0(esk3_0)
    | X1 = k9_tmap_1(esk2_0,esk3_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_28]),c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_52]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_52]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_52]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_52]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_52]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_52]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_52]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))) = k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) = k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_17]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))) = k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))) = k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_57]),c_0_19])]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(X2))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_51]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(esk2_0))) = k6_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_56]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(X1))) = k6_tmap_1(esk2_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(esk2_0))) = k6_tmap_1(X1,u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_57]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk2_0))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_51]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( k6_partfun1(u1_struct_0(X1)) = k7_tmap_1(X1,u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_57]),
    [final]).

cnf(c_0_96,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_28]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_17]),c_0_28]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_28]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_17]),c_0_18]),c_0_19])]),c_0_21]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # No proof found!
% 0.21/0.39  # SZS status CounterSatisfiable
% 0.21/0.39  # SZS output start Saturation
% 0.21/0.39  fof(t117_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_tmap_1)).
% 0.21/0.39  fof(t114_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>(u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 0.21/0.39  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.21/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.39  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.21/0.39  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.21/0.39  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.21/0.39  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.21/0.39  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.21/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))))), inference(assume_negation,[status(cth)],[t117_tmap_1])).
% 0.21/0.39  fof(c_0_11, plain, ![X20, X21, X22]:((u1_struct_0(k8_tmap_1(X20,X21))=u1_struct_0(X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(X22!=u1_struct_0(X21)|u1_pre_topc(k8_tmap_1(X20,X21))=k5_tmap_1(X20,X22))|(v2_struct_0(X21)|~m1_pre_topc(X21,X20))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.39  fof(c_0_13, plain, ![X16, X17]:(((v1_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16)))&(v2_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16))))&(l1_pre_topc(k8_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_pre_topc(X17,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.21/0.39  fof(c_0_14, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|m1_subset_1(u1_struct_0(X24),k1_zfmisc_1(u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.39  fof(c_0_15, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.21/0.39  cnf(c_0_16, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.39  cnf(c_0_22, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.21/0.39  cnf(c_0_23, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.21/0.39  cnf(c_0_24, plain, (u1_pre_topc(k8_tmap_1(X2,X3))=k5_tmap_1(X2,X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X1!=u1_struct_0(X3)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_25, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.21/0.39  fof(c_0_26, plain, ![X14, X15]:(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|k6_tmap_1(X14,X15)=g1_pre_topc(u1_struct_0(X14),k5_tmap_1(X14,X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.21/0.39  cnf(c_0_27, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_31, plain, (u1_pre_topc(k8_tmap_1(X1,X2))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25]), ['final']).
% 0.21/0.39  fof(c_0_32, plain, ![X7, X8]:(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|k7_tmap_1(X7,X8)=k6_partfun1(u1_struct_0(X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.21/0.39  fof(c_0_33, plain, ![X9, X10, X11, X12]:((X11!=k9_tmap_1(X9,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))|(X12!=u1_struct_0(X10)|r1_funct_2(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)),u1_struct_0(X9),u1_struct_0(k6_tmap_1(X9,X12)),X11,k7_tmap_1(X9,X12))))|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10))))))|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&((m1_subset_1(esk1_3(X9,X10,X11),k1_zfmisc_1(u1_struct_0(X9)))|X11=k9_tmap_1(X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10))))))|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&((esk1_3(X9,X10,X11)=u1_struct_0(X10)|X11=k9_tmap_1(X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10))))))|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r1_funct_2(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)),u1_struct_0(X9),u1_struct_0(k6_tmap_1(X9,esk1_3(X9,X10,X11))),X11,k7_tmap_1(X9,esk1_3(X9,X10,X11)))|X11=k9_tmap_1(X9,X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10)))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(k8_tmap_1(X9,X10))))))|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.21/0.39  fof(c_0_34, plain, ![X18, X19]:(((v1_funct_1(k9_tmap_1(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))&(v1_funct_2(k9_tmap_1(X18,X19),u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18))))&(m1_subset_1(k9_tmap_1(X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(k8_tmap_1(X18,X19)))))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_pre_topc(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.21/0.39  cnf(c_0_35, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)))=k8_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_17]), c_0_18]), c_0_19])]), c_0_21]), c_0_20]), ['final']).
% 0.21/0.39  cnf(c_0_38, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.21/0.39  cnf(c_0_39, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.21/0.39  cnf(c_0_40, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_41, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.21/0.39  cnf(c_0_42, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.21/0.39  cnf(c_0_43, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.21/0.39  cnf(c_0_44, plain, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X2)))=k6_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_25]), ['final']).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(esk3_0)))=k8_tmap_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_37]), ['final']).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_28]), c_0_30])]), ['final']).
% 0.21/0.39  cnf(c_0_47, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_25]), ['final']).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_49, plain, (r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])]), c_0_25]), c_0_41]), c_0_42]), c_0_43]), ['final']).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=k8_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_17]), c_0_45]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_18]), c_0_19])]), c_0_21])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_28]), c_0_48]), c_0_30])])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_17]), c_0_28]), c_0_50]), c_0_28]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_51, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_28]), ['final']).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_28]), ['final']).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_19])])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1))=k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_28]), c_0_48]), c_0_30])]), ['final']).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(X1)))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['final']).
% 0.21/0.39  cnf(c_0_61, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk1_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.21/0.39  cnf(c_0_62, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.21/0.39  cnf(c_0_63, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33]), ['final']).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_56])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_57]), c_0_19])])).
% 0.21/0.39  cnf(c_0_67, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_17])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_56]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)))=k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_25]), c_0_19])]), ['final']).
% 0.21/0.39  fof(c_0_70, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.39  cnf(c_0_71, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_72, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk2_0)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_28]), ['final']).
% 0.21/0.39  cnf(c_0_73, negated_conjecture, (X1=k9_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),X2,X1))),X1,k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),X2,X1)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)))|~v1_funct_1(X1)|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_28]), c_0_48]), c_0_30])]), ['final']).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (X1=k9_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)|m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X2,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)))|~v1_funct_1(X1)|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X2)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_28]), c_0_48]), c_0_30])]), ['final']).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,X2)=u1_struct_0(X1)|X2=k9_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))|~v1_funct_1(X2)|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_28]), c_0_48]), c_0_30])]), ['final']).
% 0.21/0.39  cnf(c_0_76, negated_conjecture, (X1=k9_tmap_1(esk2_0,esk3_0)|~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,X1))),X1,k7_tmap_1(esk2_0,esk1_3(esk2_0,esk3_0,X1)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_28]), c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_77, negated_conjecture, (X1=k9_tmap_1(esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_28]), c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (esk1_3(esk2_0,esk3_0,X1)=u1_struct_0(esk3_0)|X1=k9_tmap_1(esk2_0,esk3_0)|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_28]), c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_53, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_80, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_64, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_65, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[c_0_66, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_67, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_84, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(rw,[status(thm)],[c_0_58, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_85, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_52]), ['final']).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)))=k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_46]), ['final']).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))=k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_17]), ['final']).
% 0.21/0.39  cnf(c_0_88, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)))=k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_56]), ['final']).
% 0.21/0.39  cnf(c_0_89, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0)))=k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_57]), c_0_19])]), ['final']).
% 0.21/0.39  cnf(c_0_90, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(X2))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X2,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_51]), ['final']).
% 0.21/0.39  cnf(c_0_91, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(esk2_0)))=k6_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_56]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_92, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(X1)))=k6_tmap_1(esk2_0,u1_struct_0(X1))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_93, negated_conjecture, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(esk2_0)))=k6_tmap_1(X1,u1_struct_0(esk2_0))|v2_struct_0(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_57]), ['final']).
% 0.21/0.39  cnf(c_0_94, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk2_0))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_51]), ['final']).
% 0.21/0.39  cnf(c_0_95, negated_conjecture, (k6_partfun1(u1_struct_0(X1))=k7_tmap_1(X1,u1_struct_0(esk2_0))|v2_struct_0(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_57]), ['final']).
% 0.21/0.39  cnf(c_0_96, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70]), ['final']).
% 0.21/0.39  cnf(c_0_97, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_71, c_0_28]), ['final']).
% 0.21/0.39  cnf(c_0_98, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_17]), c_0_28]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_99, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_17]), c_0_28]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  cnf(c_0_100, negated_conjecture, (v1_funct_1(k9_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_17]), c_0_18]), c_0_19])]), c_0_21]), ['final']).
% 0.21/0.39  # SZS output end Saturation
% 0.21/0.39  # Proof object total steps             : 101
% 0.21/0.39  # Proof object clause steps            : 80
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 62
% 0.21/0.39  # Proof object clause conjectures      : 59
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 23
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 46
% 0.21/0.39  # Proof object simplifying inferences  : 128
% 0.21/0.39  # Parsed axioms                        : 10
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 23
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 23
% 0.21/0.39  # Processed clauses                    : 137
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 32
% 0.21/0.39  # ...remaining for further processing  : 104
% 0.21/0.39  # Other redundant clauses eliminated   : 3
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 1
% 0.21/0.39  # Backward-rewritten                   : 9
% 0.21/0.39  # Generated clauses                    : 84
% 0.21/0.39  # ...of the previous two non-trivial   : 91
% 0.21/0.39  # Contextual simplify-reflections      : 5
% 0.21/0.39  # Paramodulations                      : 82
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 3
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 69
% 0.21/0.39  #    Positive orientable unit clauses  : 15
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 3
% 0.21/0.39  #    Non-unit-clauses                  : 51
% 0.21/0.39  # Current number of unprocessed clauses: 0
% 0.21/0.39  # ...number of literals in the above   : 0
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 33
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1036
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 294
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 37
% 0.21/0.39  # Unit Clause-clause subsumption calls : 51
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 8
% 0.21/0.39  # BW rewrite match successes           : 4
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 5984
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.038 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.042 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
