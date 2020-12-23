%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1414+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:15 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 586 expanded)
%              Number of clauses        :   57 ( 202 expanded)
%              Number of leaves         :   15 ( 145 expanded)
%              Depth                    :   13
%              Number of atoms          :  421 (3627 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).

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

fof(dt_m1_eqrel_1,axiom,(
    ! [X1,X2] :
      ( m1_eqrel_1(X2,X1)
     => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

fof(dt_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_eqrel_1(k8_eqrel_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(cc1_eqrel_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_eqrel_1(X2,X1)
         => ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_eqrel_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(dt_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_partfun1(esk3_0,esk2_0)
    & v3_relat_2(esk3_0)
    & v8_relat_2(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & m1_subset_1(esk4_0,esk2_0)
    & m2_filter_1(esk5_0,esk2_0,esk3_0)
    & r3_binop_1(esk2_0,esk4_0,esk5_0)
    & ~ r3_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,esk4_0),k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] :
      ( ( v1_funct_1(X25)
        | ~ m2_filter_1(X25,X23,X24)
        | v1_xboole_0(X23)
        | ~ v1_relat_1(X24) )
      & ( v1_funct_2(X25,k2_zfmisc_1(X23,X23),X23)
        | ~ m2_filter_1(X25,X23,X24)
        | v1_xboole_0(X23)
        | ~ v1_relat_1(X24) )
      & ( m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X23,X23),X23)))
        | ~ m2_filter_1(X25,X23,X24)
        | v1_xboole_0(X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] :
      ( ( v1_funct_1(k3_filter_1(X13,X14,X15))
        | v1_xboole_0(X13)
        | ~ v1_partfun1(X14,X13)
        | ~ v3_relat_2(X14)
        | ~ v8_relat_2(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13))) )
      & ( v1_funct_2(k3_filter_1(X13,X14,X15),k2_zfmisc_1(k8_eqrel_1(X13,X14),k8_eqrel_1(X13,X14)),k8_eqrel_1(X13,X14))
        | v1_xboole_0(X13)
        | ~ v1_partfun1(X14,X13)
        | ~ v3_relat_2(X14)
        | ~ v8_relat_2(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13))) )
      & ( m1_subset_1(k3_filter_1(X13,X14,X15),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X13,X14),k8_eqrel_1(X13,X14)),k8_eqrel_1(X13,X14))))
        | v1_xboole_0(X13)
        | ~ v1_partfun1(X14,X13)
        | ~ v3_relat_2(X14)
        | ~ v8_relat_2(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X13,X13)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m2_filter_1(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X21,X22] :
      ( ~ m1_eqrel_1(X22,X21)
      | m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_eqrel_1])])).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ~ v3_relat_2(X17)
      | ~ v8_relat_2(X17)
      | ~ v1_partfun1(X17,X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))
      | m1_eqrel_1(k8_eqrel_1(X16,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).

fof(c_0_30,plain,(
    ! [X10,X11,X12] :
      ( ( r1_binop_1(X10,X11,X12)
        | ~ r3_binop_1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))
        | ~ m1_subset_1(X11,X10) )
      & ( r2_binop_1(X10,X11,X12)
        | ~ r3_binop_1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))
        | ~ m1_subset_1(X11,X10) )
      & ( ~ r1_binop_1(X10,X11,X12)
        | ~ r2_binop_1(X10,X11,X12)
        | r3_binop_1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,k2_zfmisc_1(X10,X10),X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X10,X10),X10)))
        | ~ m1_subset_1(X11,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_35,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_37,plain,(
    ! [X40,X41,X42,X43] :
      ( v1_xboole_0(X40)
      | ~ v1_partfun1(X41,X40)
      | ~ v3_relat_2(X41)
      | ~ v8_relat_2(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X40)))
      | ~ m1_subset_1(X42,X40)
      | ~ m2_filter_1(X43,X40,X41)
      | ~ r2_binop_1(X40,X42,X43)
      | r2_binop_1(k8_eqrel_1(X40,X41),k9_eqrel_1(X40,X41,X42),k3_filter_1(X40,X41,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_filter_1])])])])).

fof(c_0_38,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | ~ v1_xboole_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_eqrel_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( m1_eqrel_1(k8_eqrel_1(X2,X1),X2)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( v1_xboole_0(X5)
      | ~ m1_eqrel_1(X6,X5)
      | ~ v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).

cnf(c_0_42,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k3_filter_1(esk2_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk2_0,X1),k8_eqrel_1(esk2_0,X1)),k8_eqrel_1(esk2_0,X1))))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk2_0,X1,esk5_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_33]),c_0_34])]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk2_0,X1,esk5_0),k2_zfmisc_1(k8_eqrel_1(esk2_0,X1),k8_eqrel_1(esk2_0,X1)),k8_eqrel_1(esk2_0,X1))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_33]),c_0_34])]),c_0_25])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r2_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( v8_relat_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( v3_relat_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( v1_partfun1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_50,plain,(
    ! [X36,X37,X38,X39] :
      ( v1_xboole_0(X36)
      | ~ v1_partfun1(X37,X36)
      | ~ v3_relat_2(X37)
      | ~ v8_relat_2(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))
      | ~ m1_subset_1(X38,X36)
      | ~ m2_filter_1(X39,X36,X37)
      | ~ r1_binop_1(X36,X38,X39)
      | r1_binop_1(k8_eqrel_1(X36,X37),k9_eqrel_1(X36,X37,X38),k3_filter_1(X36,X37,X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_filter_1])])])])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_53,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,X32)
      | v1_xboole_0(X32)
      | r2_hidden(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_54,plain,(
    ! [X26] : m1_subset_1(esk1_1(X26),X26) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ m1_eqrel_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk2_0,X1),X2,k3_filter_1(esk2_0,X1,esk5_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ r2_binop_1(k8_eqrel_1(esk2_0,X1),X2,k3_filter_1(esk2_0,X1,esk5_0))
    | ~ r1_binop_1(k8_eqrel_1(esk2_0,X1),X2,k3_filter_1(esk2_0,X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ m1_subset_1(X2,k8_eqrel_1(esk2_0,X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( r2_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,X1),k3_filter_1(esk2_0,esk3_0,X2))
    | ~ m2_filter_1(X2,esk2_0,esk3_0)
    | ~ r2_binop_1(esk2_0,X1,X2)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_20]),c_0_47]),c_0_48]),c_0_49])]),c_0_25])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r1_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X28,X29,X30] :
      ( ( ~ m2_subset_1(X30,X28,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) )
      & ( ~ m1_subset_1(X30,X29)
        | m2_subset_1(X30,X28,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

fof(c_0_60,plain,(
    ! [X18,X19,X20] :
      ( v1_xboole_0(X18)
      | ~ v3_relat_2(X19)
      | ~ v8_relat_2(X19)
      | ~ v1_partfun1(X19,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))
      | ~ m1_subset_1(X20,X18)
      | m2_subset_1(k9_eqrel_1(X18,X19,X20),k1_zfmisc_1(X18),k8_eqrel_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k8_eqrel_1(X2,X3))
    | ~ v8_relat_2(X3)
    | ~ v3_relat_2(X3)
    | ~ v1_partfun1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_xboole_0(k8_eqrel_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,X1),k3_filter_1(esk2_0,esk3_0,esk5_0))
    | ~ r2_binop_1(esk2_0,X1,esk5_0)
    | ~ r1_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,X1),k3_filter_1(esk2_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k9_eqrel_1(esk2_0,esk3_0,X1),k8_eqrel_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_47]),c_0_48]),c_0_49]),c_0_20]),c_0_23])])).

cnf(c_0_66,negated_conjecture,
    ( r1_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,X1),k3_filter_1(esk2_0,esk3_0,X2))
    | ~ m2_filter_1(X2,esk2_0,esk3_0)
    | ~ r1_binop_1(esk2_0,X1,X2)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_20]),c_0_47]),c_0_48]),c_0_49])]),c_0_25])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,k8_eqrel_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_20]),c_0_47]),c_0_48]),c_0_49])])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_20]),c_0_47]),c_0_48]),c_0_49])]),c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,esk4_0),k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_73,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,X1),k3_filter_1(esk2_0,esk3_0,esk5_0))
    | ~ r2_binop_1(esk2_0,X1,esk5_0)
    | ~ r1_binop_1(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(k9_eqrel_1(esk2_0,esk3_0,X1),k8_eqrel_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_23])])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k8_eqrel_1(X2,X3))
    | v1_xboole_0(k8_eqrel_1(X2,X3))
    | v1_xboole_0(k1_zfmisc_1(X2))
    | ~ m2_subset_1(X1,k1_zfmisc_1(X2),k8_eqrel_1(X2,X3))
    | ~ v8_relat_2(X3)
    | ~ v3_relat_2(X3)
    | ~ v1_partfun1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_52])).

cnf(c_0_76,negated_conjecture,
    ( m2_subset_1(k9_eqrel_1(esk2_0,esk3_0,X1),k1_zfmisc_1(esk2_0),k8_eqrel_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_20]),c_0_47]),c_0_48]),c_0_49])]),c_0_25])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_binop_1(esk2_0,esk4_0,esk5_0)
    | ~ r1_binop_1(esk2_0,esk4_0,esk5_0)
    | ~ m1_subset_1(k9_eqrel_1(esk2_0,esk3_0,esk4_0),k8_eqrel_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k9_eqrel_1(esk2_0,esk3_0,X1),k8_eqrel_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_47]),c_0_48]),c_0_49]),c_0_20])]),c_0_71]),c_0_77])).

cnf(c_0_80,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_binop_1(esk2_0,esk4_0,esk5_0)
    | ~ r1_binop_1(esk2_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_74])])).

cnf(c_0_82,negated_conjecture,
    ( r2_binop_1(esk2_0,X1,esk5_0)
    | ~ r3_binop_1(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_83,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_84,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_binop_1(esk2_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_74])])).

cnf(c_0_86,negated_conjecture,
    ( r1_binop_1(esk2_0,X1,esk5_0)
    | ~ r3_binop_1(esk2_0,X1,esk5_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_83]),c_0_74])]),
    [proof]).

%------------------------------------------------------------------------------
