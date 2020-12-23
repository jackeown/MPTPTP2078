%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1798+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:46 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   71 (1229 expanded)
%              Number of clauses        :   54 ( 431 expanded)
%              Number of leaves         :    8 ( 300 expanded)
%              Depth                    :   21
%              Number of atoms          :  320 (8251 expanded)
%              Number of equality atoms :   78 (2541 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_tmap_1,conjecture,(
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

fof(dt_k5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k5_tmap_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t114_tmap_1])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      | u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) != u1_struct_0(esk2_0) )
    & ( esk4_0 = u1_struct_0(esk3_0)
      | u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) != u1_struct_0(esk2_0) )
    & ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != k5_tmap_1(esk2_0,esk4_0)
      | u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) != u1_struct_0(esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k5_tmap_1(X13,X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_tmap_1])])])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( X18 = X20
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_tmap_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(k5_tmap_1(esk2_0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | k6_tmap_1(X11,X12) = g1_pre_topc(u1_struct_0(X11),k5_tmap_1(X11,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ( v1_pre_topc(k6_tmap_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))) )
      & ( v2_pre_topc(k6_tmap_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))) )
      & ( l1_pre_topc(k6_tmap_1(X15,X16))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,X2)) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | k6_tmap_1(esk2_0,X2) != g1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_15])])).

fof(c_0_28,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_25]),c_0_14]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) != g1_pre_topc(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_33,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = u1_struct_0(esk2_0)
    | ~ v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31])]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( k5_tmap_1(esk2_0,X1) = X2
    | g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,X1)) != g1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))) = k6_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_34]),c_0_32])])).

fof(c_0_37,plain,(
    ! [X6,X7,X8,X9] :
      ( ( X8 != k8_tmap_1(X6,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X6)))
        | X9 != u1_struct_0(X7)
        | X8 = k6_tmap_1(X6,X9)
        | ~ v1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | X8 = k8_tmap_1(X6,X7)
        | ~ v1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( esk1_3(X6,X7,X8) = u1_struct_0(X7)
        | X8 = k8_tmap_1(X6,X7)
        | ~ v1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( X8 != k6_tmap_1(X6,esk1_3(X6,X7,X8))
        | X8 = k8_tmap_1(X6,X7)
        | ~ v1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( k5_tmap_1(esk2_0,X1) = u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,X1)) != k6_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k5_tmap_1(esk2_0,X1) = u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,X1)) != k6_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_42,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X2))
    | ~ l1_pre_topc(k8_tmap_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])]),c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(esk3_0))) != k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_42]),c_0_24]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_27]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))) = k8_tmap_1(esk2_0,esk3_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_24]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_48,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 = u1_struct_0(esk3_0)
    | u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) != u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),k5_tmap_1(esk2_0,u1_struct_0(esk3_0))) = k8_tmap_1(esk2_0,esk3_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_48]),c_0_14]),c_0_15])])).

cnf(c_0_54,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk4_0
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k8_tmap_1(esk2_0,esk3_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_50]),c_0_27]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != k5_tmap_1(esk2_0,esk4_0)
    | u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) != u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_58,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,esk4_0)) = k5_tmap_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k6_tmap_1(esk2_0,esk4_0) = k8_tmap_1(esk2_0,esk3_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) != k5_tmap_1(esk2_0,esk4_0)
    | ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_57]),c_0_24]),c_0_58]),c_0_14]),c_0_32]),c_0_15])]),c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_39]),c_0_27]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_24]),c_0_58]),c_0_14]),c_0_32]),c_0_15])]),c_0_12])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_39]),c_0_27]),c_0_14]),c_0_15])]),c_0_12])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k8_tmap_1(X1,X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_57]),c_0_25]),c_0_39]),c_0_48]),c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_24]),c_0_14]),c_0_15])]),c_0_12]),c_0_69]),
    [proof]).

%------------------------------------------------------------------------------
