%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 527 expanded)
%              Number of clauses        :   53 ( 185 expanded)
%              Number of leaves         :   13 ( 129 expanded)
%              Depth                    :   13
%              Number of atoms          :  407 (3284 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   27 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_filter_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m2_filter_1(X4,X1,X2)
                 => ( r3_binop_1(X1,X3,X4)
                   => r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_filter_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_m2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2) )
     => ! [X3] :
          ( m2_filter_1(X3,X1,X2)
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

fof(dt_k3_filter_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_partfun1(X2,X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & v1_funct_1(X3)
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
     => ( v1_funct_1(k3_filter_1(X1,X2,X3))
        & v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
        & m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(dt_m1_eqrel_1,axiom,(
    ! [X1,X2] :
      ( m1_eqrel_1(X2,X1)
     => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

fof(dt_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_eqrel_1(k8_eqrel_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

fof(cc1_eqrel_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_eqrel_1(X2,X1)
         => ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).

fof(d7_binop_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
         => ( r3_binop_1(X1,X2,X3)
          <=> ( r1_binop_1(X1,X2,X3)
              & r2_binop_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).

fof(dt_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(t7_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m2_filter_1(X4,X1,X2)
                 => ( r2_binop_1(X1,X3,X4)
                   => r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_filter_1)).

fof(t6_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( m2_filter_1(X4,X1,X2)
                 => ( r1_binop_1(X1,X3,X4)
                   => r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_filter_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X1)
              & v3_relat_2(X2)
              & v8_relat_2(X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ! [X4] :
                    ( m2_filter_1(X4,X1,X2)
                   => ( r3_binop_1(X1,X3,X4)
                     => r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_filter_1])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_partfun1(esk2_0,esk1_0)
    & v3_relat_2(esk2_0)
    & v8_relat_2(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & m1_subset_1(esk3_0,esk1_0)
    & m2_filter_1(esk4_0,esk1_0,esk2_0)
    & r3_binop_1(esk1_0,esk3_0,esk4_0)
    & ~ r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X28,X29,X30] :
      ( ( v1_funct_1(X30)
        | ~ m2_filter_1(X30,X28,X29)
        | v1_xboole_0(X28)
        | ~ v1_relat_1(X29) )
      & ( v1_funct_2(X30,k2_zfmisc_1(X28,X28),X28)
        | ~ m2_filter_1(X30,X28,X29)
        | v1_xboole_0(X28)
        | ~ v1_relat_1(X29) )
      & ( m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X28,X28),X28)))
        | ~ m2_filter_1(X30,X28,X29)
        | v1_xboole_0(X28)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m2_filter_1(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X18,X19,X20] :
      ( ( v1_funct_1(k3_filter_1(X18,X19,X20))
        | v1_xboole_0(X18)
        | ~ v1_partfun1(X19,X18)
        | ~ v3_relat_2(X19)
        | ~ v8_relat_2(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,k2_zfmisc_1(X18,X18),X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))) )
      & ( v1_funct_2(k3_filter_1(X18,X19,X20),k2_zfmisc_1(k8_eqrel_1(X18,X19),k8_eqrel_1(X18,X19)),k8_eqrel_1(X18,X19))
        | v1_xboole_0(X18)
        | ~ v1_partfun1(X19,X18)
        | ~ v3_relat_2(X19)
        | ~ v8_relat_2(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,k2_zfmisc_1(X18,X18),X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))) )
      & ( m1_subset_1(k3_filter_1(X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X18,X19),k8_eqrel_1(X18,X19)),k8_eqrel_1(X18,X19))))
        | v1_xboole_0(X18)
        | ~ v1_partfun1(X19,X18)
        | ~ v3_relat_2(X19)
        | ~ v8_relat_2(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,k2_zfmisc_1(X18,X18),X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0)
    | ~ v1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ( ~ m2_subset_1(X12,X10,X11)
        | m1_subset_1(X12,X11)
        | v1_xboole_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) )
      & ( ~ m1_subset_1(X12,X11)
        | m2_subset_1(X12,X10,X11)
        | v1_xboole_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

fof(c_0_28,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_29,plain,(
    ! [X26,X27] :
      ( ~ m1_eqrel_1(X27,X26)
      | m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_eqrel_1])])).

fof(c_0_30,plain,(
    ! [X21,X22] :
      ( ~ v3_relat_2(X22)
      | ~ v8_relat_2(X22)
      | ~ v1_partfun1(X22,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21)))
      | m1_eqrel_1(k8_eqrel_1(X21,X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( v1_xboole_0(X13)
      | ~ m1_eqrel_1(X14,X13)
      | ~ v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).

fof(c_0_32,plain,(
    ! [X15,X16,X17] :
      ( ( r1_binop_1(X15,X16,X17)
        | ~ r3_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ m1_subset_1(X16,X15) )
      & ( r2_binop_1(X15,X16,X17)
        | ~ r3_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ m1_subset_1(X16,X15) )
      & ( ~ r1_binop_1(X15,X16,X17)
        | ~ r2_binop_1(X15,X16,X17)
        | r3_binop_1(X15,X16,X17)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15)))
        | ~ m1_subset_1(X16,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24])]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_24])]),c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24])])).

cnf(c_0_37,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_eqrel_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( m1_eqrel_1(k8_eqrel_1(X2,X1),X2)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X23,X24,X25] :
      ( v1_xboole_0(X23)
      | ~ v3_relat_2(X24)
      | ~ v8_relat_2(X24)
      | ~ v1_partfun1(X24,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23)))
      | ~ m1_subset_1(X25,X23)
      | m2_subset_1(k9_eqrel_1(X23,X24,X25),k1_zfmisc_1(X23),k8_eqrel_1(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | ~ m1_eqrel_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k3_filter_1(esk1_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_35]),c_0_36])]),c_0_21])).

cnf(c_0_47,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_48,plain,(
    ! [X35,X36,X37,X38] :
      ( v1_xboole_0(X35)
      | ~ v1_partfun1(X36,X35)
      | ~ v3_relat_2(X36)
      | ~ v8_relat_2(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35)))
      | ~ m1_subset_1(X37,X35)
      | ~ m2_filter_1(X38,X35,X36)
      | ~ r2_binop_1(X35,X37,X38)
      | r2_binop_1(k8_eqrel_1(X35,X36),k9_eqrel_1(X35,X36,X37),k3_filter_1(X35,X36,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_filter_1])])])])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ m2_subset_1(X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( v3_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_xboole_0(k8_eqrel_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ r2_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ r1_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ m1_subset_1(X2,k8_eqrel_1(esk1_0,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_34]),c_0_35]),c_0_36])]),c_0_21])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r2_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k8_eqrel_1(X2,X3))
    | v1_xboole_0(k8_eqrel_1(X2,X3))
    | ~ v8_relat_2(X3)
    | ~ v3_relat_2(X3)
    | ~ v1_partfun1(X3,X2)
    | ~ m2_subset_1(X1,k1_zfmisc_1(X2),k8_eqrel_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( m2_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k1_zfmisc_1(esk1_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_18]),c_0_52]),c_0_53]),c_0_54])]),c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_52]),c_0_53]),c_0_54])]),c_0_21])).

fof(c_0_62,plain,(
    ! [X31,X32,X33,X34] :
      ( v1_xboole_0(X31)
      | ~ v1_partfun1(X32,X31)
      | ~ v3_relat_2(X32)
      | ~ v8_relat_2(X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X31)))
      | ~ m1_subset_1(X33,X31)
      | ~ m2_filter_1(X34,X31,X32)
      | ~ r1_binop_1(X31,X33,X34)
      | r1_binop_1(k8_eqrel_1(X31,X32),k9_eqrel_1(X31,X32,X33),k3_filter_1(X31,X32,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_filter_1])])])])).

cnf(c_0_63,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ r2_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ r1_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ m1_subset_1(X2,k8_eqrel_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r2_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ r2_binop_1(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_18]),c_0_52]),c_0_53]),c_0_54])]),c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_52]),c_0_53]),c_0_54]),c_0_18])]),c_0_61])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r1_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,esk4_0))
    | ~ r2_binop_1(esk1_0,X1,esk4_0)
    | ~ r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_52]),c_0_53]),c_0_54]),c_0_18]),c_0_20])]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ r1_binop_1(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_18]),c_0_52]),c_0_53]),c_0_54])]),c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,esk4_0))
    | ~ r2_binop_1(esk1_0,X1,esk4_0)
    | ~ r1_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_20])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_72,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_74,negated_conjecture,
    ( r2_binop_1(esk1_0,X1,esk4_0)
    | ~ r3_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_75,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_71])])).

cnf(c_0_78,negated_conjecture,
    ( r1_binop_1(esk1_0,X1,esk4_0)
    | ~ r3_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_75]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t8_filter_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r3_binop_1(X1,X3,X4)=>r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_filter_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(dt_m2_filter_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_relat_1(X2))=>![X3]:(m2_filter_1(X3,X1,X2)=>((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 0.19/0.38  fof(dt_k3_filter_1, axiom, ![X1, X2, X3]:((((((((~(v1_xboole_0(X1))&v1_partfun1(X2,X1))&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))&v1_funct_1(X3))&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>((v1_funct_1(k3_filter_1(X1,X2,X3))&v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))&m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 0.19/0.38  fof(redefinition_m2_subset_1, axiom, ![X1, X2]:(((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(X1)))=>![X3]:(m2_subset_1(X3,X1,X2)<=>m1_subset_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 0.19/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.38  fof(dt_m1_eqrel_1, axiom, ![X1, X2]:(m1_eqrel_1(X2,X1)=>m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_eqrel_1)).
% 0.19/0.38  fof(dt_k8_eqrel_1, axiom, ![X1, X2]:((((v3_relat_2(X2)&v8_relat_2(X2))&v1_partfun1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>m1_eqrel_1(k8_eqrel_1(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_eqrel_1)).
% 0.19/0.38  fof(cc1_eqrel_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_eqrel_1(X2,X1)=>~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_eqrel_1)).
% 0.19/0.38  fof(d7_binop_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>(r3_binop_1(X1,X2,X3)<=>(r1_binop_1(X1,X2,X3)&r2_binop_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_binop_1)).
% 0.19/0.38  fof(dt_k9_eqrel_1, axiom, ![X1, X2, X3]:((((((~(v1_xboole_0(X1))&v3_relat_2(X2))&v8_relat_2(X2))&v1_partfun1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))&m1_subset_1(X3,X1))=>m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 0.19/0.38  fof(t7_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r2_binop_1(X1,X3,X4)=>r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_filter_1)).
% 0.19/0.38  fof(t6_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r1_binop_1(X1,X3,X4)=>r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_filter_1)).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r3_binop_1(X1,X3,X4)=>r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4)))))))), inference(assume_negation,[status(cth)],[t8_filter_1])).
% 0.19/0.38  fof(c_0_14, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|v1_relat_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, (~v1_xboole_0(esk1_0)&((((v1_partfun1(esk2_0,esk1_0)&v3_relat_2(esk2_0))&v8_relat_2(esk2_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(m1_subset_1(esk3_0,esk1_0)&(m2_filter_1(esk4_0,esk1_0,esk2_0)&(r3_binop_1(esk1_0,esk3_0,esk4_0)&~r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X28, X29, X30]:(((v1_funct_1(X30)|~m2_filter_1(X30,X28,X29)|(v1_xboole_0(X28)|~v1_relat_1(X29)))&(v1_funct_2(X30,k2_zfmisc_1(X28,X28),X28)|~m2_filter_1(X30,X28,X29)|(v1_xboole_0(X28)|~v1_relat_1(X29))))&(m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X28,X28),X28)))|~m2_filter_1(X30,X28,X29)|(v1_xboole_0(X28)|~v1_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).
% 0.19/0.38  cnf(c_0_17, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_19, plain, (v1_funct_1(X1)|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (m2_filter_1(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_22, plain, ![X18, X19, X20]:(((v1_funct_1(k3_filter_1(X18,X19,X20))|(v1_xboole_0(X18)|~v1_partfun1(X19,X18)|~v3_relat_2(X19)|~v8_relat_2(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,k2_zfmisc_1(X18,X18),X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18)))))&(v1_funct_2(k3_filter_1(X18,X19,X20),k2_zfmisc_1(k8_eqrel_1(X18,X19),k8_eqrel_1(X18,X19)),k8_eqrel_1(X18,X19))|(v1_xboole_0(X18)|~v1_partfun1(X19,X18)|~v3_relat_2(X19)|~v8_relat_2(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,k2_zfmisc_1(X18,X18),X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18))))))&(m1_subset_1(k3_filter_1(X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X18,X19),k8_eqrel_1(X18,X19)),k8_eqrel_1(X18,X19))))|(v1_xboole_0(X18)|~v1_partfun1(X19,X18)|~v3_relat_2(X19)|~v8_relat_2(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,k2_zfmisc_1(X18,X18),X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X18,X18),X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).
% 0.19/0.38  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_25, plain, (v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk4_0)|~v1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.38  fof(c_0_27, plain, ![X10, X11, X12]:((~m2_subset_1(X12,X10,X11)|m1_subset_1(X12,X11)|(v1_xboole_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(X10))))&(~m1_subset_1(X12,X11)|m2_subset_1(X12,X10,X11)|(v1_xboole_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).
% 0.19/0.38  fof(c_0_28, plain, ![X5, X6]:(~v1_xboole_0(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.38  fof(c_0_29, plain, ![X26, X27]:(~m1_eqrel_1(X27,X26)|m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_eqrel_1])])).
% 0.19/0.38  fof(c_0_30, plain, ![X21, X22]:(~v3_relat_2(X22)|~v8_relat_2(X22)|~v1_partfun1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21)))|m1_eqrel_1(k8_eqrel_1(X21,X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).
% 0.19/0.38  fof(c_0_31, plain, ![X13, X14]:(v1_xboole_0(X13)|(~m1_eqrel_1(X14,X13)|~v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).
% 0.19/0.38  fof(c_0_32, plain, ![X15, X16, X17]:(((r1_binop_1(X15,X16,X17)|~r3_binop_1(X15,X16,X17)|(~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|~m1_subset_1(X16,X15))&(r2_binop_1(X15,X16,X17)|~r3_binop_1(X15,X16,X17)|(~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|~m1_subset_1(X16,X15)))&(~r1_binop_1(X15,X16,X17)|~r2_binop_1(X15,X16,X17)|r3_binop_1(X15,X16,X17)|(~v1_funct_1(X17)|~v1_funct_2(X17,k2_zfmisc_1(X15,X15),X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X15,X15),X15))))|~m1_subset_1(X16,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).
% 0.19/0.38  cnf(c_0_33, plain, (m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_24])]), c_0_21])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_24])]), c_0_21])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_24])])).
% 0.19/0.38  cnf(c_0_37, plain, (v1_funct_1(k3_filter_1(X1,X2,X3))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_38, plain, (m1_subset_1(X1,X3)|v1_xboole_0(X2)|v1_xboole_0(X3)|~m2_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_39, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_eqrel_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_41, plain, (m1_eqrel_1(k8_eqrel_1(X2,X1),X2)|~v3_relat_2(X1)|~v8_relat_2(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  fof(c_0_42, plain, ![X23, X24, X25]:(v1_xboole_0(X23)|~v3_relat_2(X24)|~v8_relat_2(X24)|~v1_partfun1(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X23,X23)))|~m1_subset_1(X25,X23)|m2_subset_1(k9_eqrel_1(X23,X24,X25),k1_zfmisc_1(X23),k8_eqrel_1(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).
% 0.19/0.38  cnf(c_0_43, plain, (v1_xboole_0(X1)|~m1_eqrel_1(X2,X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_44, plain, (r3_binop_1(X1,X2,X3)|~r1_binop_1(X1,X2,X3)|~r2_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(k3_filter_1(esk1_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_21])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (v1_funct_1(k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_35]), c_0_36])]), c_0_21])).
% 0.19/0.38  cnf(c_0_47, plain, (v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_48, plain, ![X35, X36, X37, X38]:(v1_xboole_0(X35)|(~v1_partfun1(X36,X35)|~v3_relat_2(X36)|~v8_relat_2(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35)))|(~m1_subset_1(X37,X35)|(~m2_filter_1(X38,X35,X36)|(~r2_binop_1(X35,X37,X38)|r2_binop_1(k8_eqrel_1(X35,X36),k9_eqrel_1(X35,X36,X37),k3_filter_1(X35,X36,X38))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_filter_1])])])])).
% 0.19/0.38  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~m2_subset_1(X1,X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_50, plain, (m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v8_relat_2(X2)|~v3_relat_2(X2)|~v1_partfun1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_51, plain, (v1_xboole_0(X1)|m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))|~v3_relat_2(X2)|~v8_relat_2(X2)|~v1_partfun1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (v8_relat_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (v3_relat_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (v1_partfun1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v8_relat_2(X2)|~v3_relat_2(X2)|~v1_partfun1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_xboole_0(k8_eqrel_1(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_41])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (r3_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~r2_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~r1_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))|~m1_subset_1(X2,k8_eqrel_1(esk1_0,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_34]), c_0_35]), c_0_36])]), c_0_21])).
% 0.19/0.38  cnf(c_0_58, plain, (v1_xboole_0(X1)|r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,X1)|~m2_filter_1(X4,X1,X2)|~r2_binop_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.38  cnf(c_0_59, plain, (m1_subset_1(X1,k8_eqrel_1(X2,X3))|v1_xboole_0(k8_eqrel_1(X2,X3))|~v8_relat_2(X3)|~v3_relat_2(X3)|~v1_partfun1(X3,X2)|~m2_subset_1(X1,k1_zfmisc_1(X2),k8_eqrel_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (m2_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k1_zfmisc_1(esk1_0),k8_eqrel_1(esk1_0,esk2_0))|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_18]), c_0_52]), c_0_53]), c_0_54])]), c_0_21])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(k8_eqrel_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_18]), c_0_52]), c_0_53]), c_0_54])]), c_0_21])).
% 0.19/0.38  fof(c_0_62, plain, ![X31, X32, X33, X34]:(v1_xboole_0(X31)|(~v1_partfun1(X32,X31)|~v3_relat_2(X32)|~v8_relat_2(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X31)))|(~m1_subset_1(X33,X31)|(~m2_filter_1(X34,X31,X32)|(~r1_binop_1(X31,X33,X34)|r1_binop_1(k8_eqrel_1(X31,X32),k9_eqrel_1(X31,X32,X33),k3_filter_1(X31,X32,X34))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_filter_1])])])])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (r3_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~r2_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~r1_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))|~m1_subset_1(X2,k8_eqrel_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (r2_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~r2_binop_1(esk1_0,X1,X2)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_18]), c_0_52]), c_0_53]), c_0_54])]), c_0_21])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_52]), c_0_53]), c_0_54]), c_0_18])]), c_0_61])).
% 0.19/0.38  cnf(c_0_66, plain, (v1_xboole_0(X1)|r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,X1)|~m2_filter_1(X4,X1,X2)|~r1_binop_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,esk4_0))|~r2_binop_1(esk1_0,X1,esk4_0)|~r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,esk4_0))|~m1_subset_1(X1,esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_52]), c_0_53]), c_0_54]), c_0_18]), c_0_20])]), c_0_65])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~r1_binop_1(esk1_0,X1,X2)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_18]), c_0_52]), c_0_53]), c_0_54])]), c_0_21])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (~r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,esk4_0))|~r2_binop_1(esk1_0,X1,esk4_0)|~r1_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_20])])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_72, plain, (r2_binop_1(X1,X2,X3)|~r3_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk4_0)|~r1_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (r2_binop_1(esk1_0,X1,esk4_0)|~r3_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_34]), c_0_35]), c_0_36])])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (r3_binop_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_76, plain, (r1_binop_1(X1,X2,X3)|~r3_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (~r1_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_71])])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (r1_binop_1(esk1_0,X1,esk4_0)|~r3_binop_1(esk1_0,X1,esk4_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_34]), c_0_35]), c_0_36])])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_75]), c_0_71])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 80
% 0.19/0.38  # Proof object clause steps            : 53
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 34
% 0.19/0.38  # Proof object clause conjectures      : 31
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 27
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 24
% 0.19/0.38  # Proof object simplifying inferences  : 72
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 28
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 28
% 0.19/0.38  # Processed clauses                    : 102
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 102
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 3
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 53
% 0.19/0.38  # ...of the previous two non-trivial   : 49
% 0.19/0.38  # Contextual simplify-reflections      : 7
% 0.19/0.38  # Paramodulations                      : 53
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 70
% 0.19/0.38  #    Positive orientable unit clauses  : 12
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 53
% 0.19/0.38  # Current number of unprocessed clauses: 3
% 0.19/0.38  # ...number of literals in the above   : 34
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 32
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2262
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 179
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.38  # Unit Clause-clause subsumption calls : 86
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6295
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
