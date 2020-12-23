%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:25 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 401 expanded)
%              Number of clauses        :   38 ( 137 expanded)
%              Number of leaves         :    7 ( 101 expanded)
%              Depth                    :    6
%              Number of atoms          :  284 (2116 expanded)
%              Number of equality atoms :   37 ( 134 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    7 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( ( u1_struct_0(k6_tmap_1(X15,X16)) = u1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( u1_pre_topc(k6_tmap_1(X15,X16)) = k5_tmap_1(X15,X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | m1_subset_1(u1_struct_0(X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

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

cnf(c_0_10,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | k7_tmap_1(X6,X7) = k6_partfun1(u1_struct_0(X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_14,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

fof(c_0_20,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X10 != k9_tmap_1(X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | X11 != u1_struct_0(X9)
        | r1_funct_2(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)),u1_struct_0(X8),u1_struct_0(k6_tmap_1(X8,X11)),X10,k7_tmap_1(X8,X11))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))))
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))
        | X10 = k9_tmap_1(X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))))
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( esk1_3(X8,X9,X10) = u1_struct_0(X9)
        | X10 = k9_tmap_1(X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))))
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r1_funct_2(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)),u1_struct_0(X8),u1_struct_0(k6_tmap_1(X8,esk1_3(X8,X9,X10))),X10,k7_tmap_1(X8,esk1_3(X8,X9,X10)))
        | X10 = k9_tmap_1(X8,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))))
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ( v1_funct_1(k9_tmap_1(X13,X14))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | ~ m1_pre_topc(X14,X13) )
      & ( v1_funct_2(k9_tmap_1(X13,X14),u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | ~ m1_pre_topc(X14,X13) )
      & ( m1_subset_1(k9_tmap_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | ~ m1_pre_topc(X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).

cnf(c_0_23,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11]),
    [final]).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_26,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_27,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_28,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_29,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_31,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).

fof(c_0_34,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,plain,
    ( r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])]),c_0_11]),c_0_25]),c_0_26]),c_0_27]),
    [final]).

cnf(c_0_36,plain,
    ( u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2))) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_11]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( X1 = k9_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2,X1))),X1,k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2,X1)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( X1 = k9_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)
    | m1_subset_1(esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2) = u1_struct_0(X1)
    | X2 = k9_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X1,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)))))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)) = k5_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)) = u1_struct_0(esk2_0)
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_22]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22]),
    [final]).

cnf(c_0_45,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_22]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.13/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.38  fof(t117_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_tmap_1)).
% 0.13/0.38  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.13/0.38  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.13/0.38  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(c_0_7, plain, ![X15, X16]:((u1_struct_0(k6_tmap_1(X15,X16))=u1_struct_0(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(u1_pre_topc(k6_tmap_1(X15,X16))=k5_tmap_1(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|m1_subset_1(u1_struct_0(X18),k1_zfmisc_1(u1_struct_0(X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))))), inference(assume_negation,[status(cth)],[t117_tmap_1])).
% 0.13/0.38  cnf(c_0_10, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_11, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X6, X7]:(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|(~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))|k7_tmap_1(X6,X7)=k6_partfun1(u1_struct_0(X6)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.13/0.38  fof(c_0_20, plain, ![X8, X9, X10, X11]:((X10!=k9_tmap_1(X8,X9)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))|(X11!=u1_struct_0(X9)|r1_funct_2(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)),u1_struct_0(X8),u1_struct_0(k6_tmap_1(X8,X11)),X10,k7_tmap_1(X8,X11))))|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9))))))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&((m1_subset_1(esk1_3(X8,X9,X10),k1_zfmisc_1(u1_struct_0(X8)))|X10=k9_tmap_1(X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9))))))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&((esk1_3(X8,X9,X10)=u1_struct_0(X9)|X10=k9_tmap_1(X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9))))))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(~r1_funct_2(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)),u1_struct_0(X8),u1_struct_0(k6_tmap_1(X8,esk1_3(X8,X9,X10))),X10,k7_tmap_1(X8,esk1_3(X8,X9,X10)))|X10=k9_tmap_1(X8,X9)|(~v1_funct_1(X10)|~v1_funct_2(X10,u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9)))|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(k8_tmap_1(X8,X9))))))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X13, X14]:(((v1_funct_1(k9_tmap_1(X13,X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_pre_topc(X14,X13)))&(v1_funct_2(k9_tmap_1(X13,X14),u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_pre_topc(X14,X13))))&(m1_subset_1(k9_tmap_1(X13,X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(k8_tmap_1(X13,X14)))))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_pre_topc(X14,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_24, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_26, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_27, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_29, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk1_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk1_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.38  cnf(c_0_30, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.38  cnf(c_0_31, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  fof(c_0_34, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])]), c_0_11]), c_0_25]), c_0_26]), c_0_27]), ['final']).
% 0.13/0.38  cnf(c_0_36, plain, (u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_11]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (X1=k9_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2,X1))),X1,k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2,X1)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))|~v1_funct_1(X1)|~m1_pre_topc(X2,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_29, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (X1=k9_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)|m1_subset_1(esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))|~v1_funct_1(X1)|~m1_pre_topc(X2,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X2)))))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (esk1_3(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2)=u1_struct_0(X1)|X2=k9_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)))|~v1_funct_1(X2)|~m1_pre_topc(X1,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)))))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_32, c_0_33]), ['final']).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (u1_pre_topc(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1))=k5_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_28, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1))=u1_struct_0(esk2_0)|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_10, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_11, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_11, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_45, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34]), ['final']).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_15]), c_0_22]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))=k5_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (v1_funct_1(k9_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_15]), c_0_16]), c_0_17])]), c_0_18]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 53
% 0.13/0.38  # Proof object clause steps            : 38
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 36
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 57
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 56
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 1
% 0.13/0.38  # Generated clauses                    : 20
% 0.13/0.38  # ...of the previous two non-trivial   : 21
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 19
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 36
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 19
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 594
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 13
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 5
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3697
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
