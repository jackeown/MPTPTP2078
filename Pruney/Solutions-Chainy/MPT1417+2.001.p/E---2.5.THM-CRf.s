%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:52 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 767 expanded)
%              Number of clauses        :   46 ( 274 expanded)
%              Number of leaves         :    7 ( 188 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 (4730 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   27 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_filter_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m2_filter_1(X3,X1,X2)
             => ! [X4] :
                  ( m2_filter_1(X4,X1,X2)
                 => ( r6_binop_1(X1,X3,X4)
                   => r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_filter_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_m2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2) )
     => ! [X3] :
          ( m2_filter_1(X3,X1,X2)
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).

fof(d11_binop_1,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
         => ( r6_binop_1(X1,X2,X3)
          <=> ( r4_binop_1(X1,X2,X3)
              & r5_binop_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_binop_1)).

fof(t10_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m2_filter_1(X3,X1,X2)
             => ! [X4] :
                  ( m2_filter_1(X4,X1,X2)
                 => ( r5_binop_1(X1,X3,X4)
                   => r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_filter_1)).

fof(t9_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( m2_filter_1(X3,X1,X2)
             => ! [X4] :
                  ( m2_filter_1(X4,X1,X2)
                 => ( r4_binop_1(X1,X3,X4)
                   => r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_filter_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X1)
              & v3_relat_2(X2)
              & v8_relat_2(X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ! [X3] :
                ( m2_filter_1(X3,X1,X2)
               => ! [X4] :
                    ( m2_filter_1(X4,X1,X2)
                   => ( r6_binop_1(X1,X3,X4)
                     => r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_filter_1])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_9,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_partfun1(esk2_0,esk1_0)
    & v3_relat_2(esk2_0)
    & v8_relat_2(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & m2_filter_1(esk3_0,esk1_0,esk2_0)
    & m2_filter_1(esk4_0,esk1_0,esk2_0)
    & r6_binop_1(esk1_0,esk3_0,esk4_0)
    & ~ r6_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ( v1_funct_1(X16)
        | ~ m2_filter_1(X16,X14,X15)
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X15) )
      & ( v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)
        | ~ m2_filter_1(X16,X14,X15)
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X15) )
      & ( m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))
        | ~ m2_filter_1(X16,X14,X15)
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_11,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m2_filter_1(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ( v1_funct_1(k3_filter_1(X11,X12,X13))
        | v1_xboole_0(X11)
        | ~ v1_partfun1(X12,X11)
        | ~ v3_relat_2(X12)
        | ~ v8_relat_2(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) )
      & ( v1_funct_2(k3_filter_1(X11,X12,X13),k2_zfmisc_1(k8_eqrel_1(X11,X12),k8_eqrel_1(X11,X12)),k8_eqrel_1(X11,X12))
        | v1_xboole_0(X11)
        | ~ v1_partfun1(X12,X11)
        | ~ v3_relat_2(X12)
        | ~ v8_relat_2(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) )
      & ( m1_subset_1(k3_filter_1(X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X11,X12),k8_eqrel_1(X11,X12)),k8_eqrel_1(X11,X12))))
        | v1_xboole_0(X11)
        | ~ v1_partfun1(X12,X11)
        | ~ v3_relat_2(X12)
        | ~ v8_relat_2(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    | ~ v1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m2_filter_1(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_22,plain,(
    ! [X8,X9,X10] :
      ( ( r4_binop_1(X8,X9,X10)
        | ~ r6_binop_1(X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,k2_zfmisc_1(X8,X8),X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,k2_zfmisc_1(X8,X8),X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))) )
      & ( r5_binop_1(X8,X9,X10)
        | ~ r6_binop_1(X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,k2_zfmisc_1(X8,X8),X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,k2_zfmisc_1(X8,X8),X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))) )
      & ( ~ r4_binop_1(X8,X9,X10)
        | ~ r5_binop_1(X8,X9,X10)
        | r6_binop_1(X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,k2_zfmisc_1(X8,X8),X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,k2_zfmisc_1(X8,X8),X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_binop_1])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_18])]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_18])]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18])])).

cnf(c_0_27,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0)
    | ~ v1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_15])).

cnf(c_0_30,plain,
    ( r6_binop_1(X1,X2,X3)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k3_filter_1(esk1_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_25]),c_0_26])]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_26])]),c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_21]),c_0_18])]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_21]),c_0_18])]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_18])])).

fof(c_0_37,plain,(
    ! [X17,X18,X19,X20] :
      ( v1_xboole_0(X17)
      | ~ v1_partfun1(X18,X17)
      | ~ v3_relat_2(X18)
      | ~ v8_relat_2(X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X17)))
      | ~ m2_filter_1(X19,X17,X18)
      | ~ m2_filter_1(X20,X17,X18)
      | ~ r5_binop_1(X17,X19,X20)
      | r5_binop_1(k8_eqrel_1(X17,X18),k3_filter_1(X17,X18,X19),k3_filter_1(X17,X18,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_filter_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( r6_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ r5_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ r4_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v1_funct_2(X2,k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k3_filter_1(esk1_0,X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_34]),c_0_35]),c_0_36])]),c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk1_0,X1,esk3_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_35]),c_0_36])]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk1_0,X1,esk3_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_35]),c_0_36])]),c_0_15])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r5_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( v3_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_46,plain,(
    ! [X21,X22,X23,X24] :
      ( v1_xboole_0(X21)
      | ~ v1_partfun1(X22,X21)
      | ~ v3_relat_2(X22)
      | ~ v8_relat_2(X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21)))
      | ~ m2_filter_1(X23,X21,X22)
      | ~ m2_filter_1(X24,X21,X22)
      | ~ r4_binop_1(X21,X23,X24)
      | r4_binop_1(k8_eqrel_1(X21,X22),k3_filter_1(X21,X22,X23),k3_filter_1(X21,X22,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_filter_1])])])])).

cnf(c_0_47,negated_conjecture,
    ( r6_binop_1(k8_eqrel_1(esk1_0,X1),k3_filter_1(esk1_0,X1,esk3_0),k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ r5_binop_1(k8_eqrel_1(esk1_0,X1),k3_filter_1(esk1_0,X1,esk3_0),k3_filter_1(esk1_0,X1,esk4_0))
    | ~ r4_binop_1(k8_eqrel_1(esk1_0,X1),k3_filter_1(esk1_0,X1,esk3_0),k3_filter_1(esk1_0,X1,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r5_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ m2_filter_1(X1,esk1_0,esk2_0)
    | ~ r5_binop_1(esk1_0,X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_12]),c_0_43]),c_0_44]),c_0_45])]),c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( ~ r6_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r4_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ r5_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r4_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43]),c_0_44]),c_0_45]),c_0_12]),c_0_14]),c_0_21])]),c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( r4_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ m2_filter_1(X1,esk1_0,esk2_0)
    | ~ r4_binop_1(esk1_0,X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_12]),c_0_43]),c_0_44]),c_0_45])]),c_0_15])).

cnf(c_0_53,plain,
    ( r5_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( ~ r5_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r4_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_14]),c_0_21])])).

cnf(c_0_55,negated_conjecture,
    ( r5_binop_1(esk1_0,X1,esk4_0)
    | ~ r6_binop_1(esk1_0,X1,esk4_0)
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_56,negated_conjecture,
    ( r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_57,plain,
    ( r4_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( ~ r4_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_35]),c_0_36]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( r4_binop_1(esk1_0,X1,esk4_0)
    | ~ r6_binop_1(esk1_0,X1,esk4_0)
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_56]),c_0_35]),c_0_36]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t11_filter_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m2_filter_1(X3,X1,X2)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r6_binop_1(X1,X3,X4)=>r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_filter_1)).
% 0.12/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.38  fof(dt_m2_filter_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_relat_1(X2))=>![X3]:(m2_filter_1(X3,X1,X2)=>((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 0.12/0.38  fof(dt_k3_filter_1, axiom, ![X1, X2, X3]:((((((((~(v1_xboole_0(X1))&v1_partfun1(X2,X1))&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))&v1_funct_1(X3))&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>((v1_funct_1(k3_filter_1(X1,X2,X3))&v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))&m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 0.12/0.38  fof(d11_binop_1, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>(r6_binop_1(X1,X2,X3)<=>(r4_binop_1(X1,X2,X3)&r5_binop_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_binop_1)).
% 0.12/0.38  fof(t10_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m2_filter_1(X3,X1,X2)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r5_binop_1(X1,X3,X4)=>r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_filter_1)).
% 0.12/0.38  fof(t9_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m2_filter_1(X3,X1,X2)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r4_binop_1(X1,X3,X4)=>r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_filter_1)).
% 0.12/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m2_filter_1(X3,X1,X2)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r6_binop_1(X1,X3,X4)=>r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4)))))))), inference(assume_negation,[status(cth)],[t11_filter_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X5, X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|v1_relat_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.38  fof(c_0_9, negated_conjecture, (~v1_xboole_0(esk1_0)&((((v1_partfun1(esk2_0,esk1_0)&v3_relat_2(esk2_0))&v8_relat_2(esk2_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(m2_filter_1(esk3_0,esk1_0,esk2_0)&(m2_filter_1(esk4_0,esk1_0,esk2_0)&(r6_binop_1(esk1_0,esk3_0,esk4_0)&~r6_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.12/0.38  fof(c_0_10, plain, ![X14, X15, X16]:(((v1_funct_1(X16)|~m2_filter_1(X16,X14,X15)|(v1_xboole_0(X14)|~v1_relat_1(X15)))&(v1_funct_2(X16,k2_zfmisc_1(X14,X14),X14)|~m2_filter_1(X16,X14,X15)|(v1_xboole_0(X14)|~v1_relat_1(X15))))&(m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X14,X14),X14)))|~m2_filter_1(X16,X14,X15)|(v1_xboole_0(X14)|~v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).
% 0.12/0.38  cnf(c_0_11, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_13, plain, (v1_funct_1(X1)|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (m2_filter_1(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  fof(c_0_16, plain, ![X11, X12, X13]:(((v1_funct_1(k3_filter_1(X11,X12,X13))|(v1_xboole_0(X11)|~v1_partfun1(X12,X11)|~v3_relat_2(X12)|~v8_relat_2(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11)))|~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))))&(v1_funct_2(k3_filter_1(X11,X12,X13),k2_zfmisc_1(k8_eqrel_1(X11,X12),k8_eqrel_1(X11,X12)),k8_eqrel_1(X11,X12))|(v1_xboole_0(X11)|~v1_partfun1(X12,X11)|~v3_relat_2(X12)|~v8_relat_2(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11)))|~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))))))&(m1_subset_1(k3_filter_1(X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X11,X12),k8_eqrel_1(X11,X12)),k8_eqrel_1(X11,X12))))|(v1_xboole_0(X11)|~v1_partfun1(X12,X11)|~v3_relat_2(X12)|~v8_relat_2(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X11)))|~v1_funct_1(X13)|~v1_funct_2(X13,k2_zfmisc_1(X11,X11),X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).
% 0.12/0.38  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.38  cnf(c_0_19, plain, (v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk4_0)|~v1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (m2_filter_1(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  fof(c_0_22, plain, ![X8, X9, X10]:(((r4_binop_1(X8,X9,X10)|~r6_binop_1(X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,k2_zfmisc_1(X8,X8),X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,k2_zfmisc_1(X8,X8),X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8)))))&(r5_binop_1(X8,X9,X10)|~r6_binop_1(X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,k2_zfmisc_1(X8,X8),X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,k2_zfmisc_1(X8,X8),X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))))))&(~r4_binop_1(X8,X9,X10)|~r5_binop_1(X8,X9,X10)|r6_binop_1(X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,k2_zfmisc_1(X8,X8),X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,k2_zfmisc_1(X8,X8),X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X8),X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_binop_1])])])])).
% 0.12/0.38  cnf(c_0_23, plain, (m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_14]), c_0_18])]), c_0_15])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_14]), c_0_18])]), c_0_15])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18])])).
% 0.12/0.38  cnf(c_0_27, plain, (v1_funct_1(k3_filter_1(X1,X2,X3))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_28, plain, (v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk3_0)|~v1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_21]), c_0_15])).
% 0.12/0.38  cnf(c_0_30, plain, (r6_binop_1(X1,X2,X3)|~r4_binop_1(X1,X2,X3)|~r5_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(k3_filter_1(esk1_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_15])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_25]), c_0_26])]), c_0_15])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25]), c_0_26])]), c_0_15])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_21]), c_0_18])]), c_0_15])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_21]), c_0_18])]), c_0_15])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_18])])).
% 0.12/0.38  fof(c_0_37, plain, ![X17, X18, X19, X20]:(v1_xboole_0(X17)|(~v1_partfun1(X18,X17)|~v3_relat_2(X18)|~v8_relat_2(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X17)))|(~m2_filter_1(X19,X17,X18)|(~m2_filter_1(X20,X17,X18)|(~r5_binop_1(X17,X19,X20)|r5_binop_1(k8_eqrel_1(X17,X18),k3_filter_1(X17,X18,X19),k3_filter_1(X17,X18,X20))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_filter_1])])])])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r6_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~r5_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~r4_binop_1(k8_eqrel_1(esk1_0,X1),X2,k3_filter_1(esk1_0,X1,esk4_0))|~v1_funct_2(X2,k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(k3_filter_1(esk1_0,X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_34]), c_0_35]), c_0_36])]), c_0_15])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (v1_funct_1(k3_filter_1(esk1_0,X1,esk3_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_35]), c_0_36])]), c_0_15])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (v1_funct_2(k3_filter_1(esk1_0,X1,esk3_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_35]), c_0_36])]), c_0_15])).
% 0.12/0.38  cnf(c_0_42, plain, (v1_xboole_0(X1)|r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m2_filter_1(X3,X1,X2)|~m2_filter_1(X4,X1,X2)|~r5_binop_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (v8_relat_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (v3_relat_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (v1_partfun1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  fof(c_0_46, plain, ![X21, X22, X23, X24]:(v1_xboole_0(X21)|(~v1_partfun1(X22,X21)|~v3_relat_2(X22)|~v8_relat_2(X22)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21)))|(~m2_filter_1(X23,X21,X22)|(~m2_filter_1(X24,X21,X22)|(~r4_binop_1(X21,X23,X24)|r4_binop_1(k8_eqrel_1(X21,X22),k3_filter_1(X21,X22,X23),k3_filter_1(X21,X22,X24))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_filter_1])])])])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (r6_binop_1(k8_eqrel_1(esk1_0,X1),k3_filter_1(esk1_0,X1,esk3_0),k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~r5_binop_1(k8_eqrel_1(esk1_0,X1),k3_filter_1(esk1_0,X1,esk3_0),k3_filter_1(esk1_0,X1,esk4_0))|~r4_binop_1(k8_eqrel_1(esk1_0,X1),k3_filter_1(esk1_0,X1,esk3_0),k3_filter_1(esk1_0,X1,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (r5_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~m2_filter_1(X1,esk1_0,esk2_0)|~r5_binop_1(esk1_0,X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_12]), c_0_43]), c_0_44]), c_0_45])]), c_0_15])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (~r6_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_50, plain, (v1_xboole_0(X1)|r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m2_filter_1(X3,X1,X2)|~m2_filter_1(X4,X1,X2)|~r4_binop_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (~r5_binop_1(esk1_0,esk3_0,esk4_0)|~r4_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_43]), c_0_44]), c_0_45]), c_0_12]), c_0_14]), c_0_21])]), c_0_49])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (r4_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~m2_filter_1(X1,esk1_0,esk2_0)|~r4_binop_1(esk1_0,X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_12]), c_0_43]), c_0_44]), c_0_45])]), c_0_15])).
% 0.12/0.38  cnf(c_0_53, plain, (r5_binop_1(X1,X2,X3)|~r6_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (~r5_binop_1(esk1_0,esk3_0,esk4_0)|~r4_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_14]), c_0_21])])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (r5_binop_1(esk1_0,X1,esk4_0)|~r6_binop_1(esk1_0,X1,esk4_0)|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_24]), c_0_25]), c_0_26])])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (r6_binop_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_57, plain, (r4_binop_1(X1,X2,X3)|~r6_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (~r4_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_35]), c_0_36]), c_0_34])])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (r4_binop_1(esk1_0,X1,esk4_0)|~r6_binop_1(esk1_0,X1,esk4_0)|~v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_24]), c_0_25]), c_0_26])])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_56]), c_0_35]), c_0_36]), c_0_34])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 61
% 0.12/0.38  # Proof object clause steps            : 46
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 37
% 0.12/0.38  # Proof object clause conjectures      : 34
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 21
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 23
% 0.12/0.38  # Proof object simplifying inferences  : 83
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 21
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 21
% 0.12/0.38  # Processed clauses                    : 76
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 76
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 45
% 0.12/0.38  # ...of the previous two non-trivial   : 44
% 0.12/0.38  # Contextual simplify-reflections      : 8
% 0.12/0.38  # Paramodulations                      : 45
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 53
% 0.12/0.38  #    Positive orientable unit clauses  : 16
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 34
% 0.12/0.38  # Current number of unprocessed clauses: 10
% 0.12/0.38  # ...number of literals in the above   : 113
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 23
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 618
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 24
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.38  # Unit Clause-clause subsumption calls : 26
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 5315
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.035 s
% 0.12/0.38  # System time              : 0.003 s
% 0.12/0.38  # Total time               : 0.038 s
% 0.12/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
