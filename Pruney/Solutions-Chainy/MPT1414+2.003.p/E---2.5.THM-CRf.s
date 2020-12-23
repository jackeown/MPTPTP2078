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
% DateTime   : Thu Dec  3 11:14:51 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 570 expanded)
%              Number of clauses        :   52 ( 192 expanded)
%              Number of leaves         :   13 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  423 (3628 expanded)
%              Number of equality atoms :    3 (   6 expanded)
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

fof(dt_k7_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_subset_1(k7_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(redefinition_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k8_eqrel_1(X1,X2) = k7_eqrel_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(fc3_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ~ v1_xboole_0(k7_eqrel_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_eqrel_1)).

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
    ! [X13,X14,X15] :
      ( ( r1_binop_1(X13,X14,X15)
        | ~ r3_binop_1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13)))
        | ~ m1_subset_1(X14,X13) )
      & ( r2_binop_1(X13,X14,X15)
        | ~ r3_binop_1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13)))
        | ~ m1_subset_1(X14,X13) )
      & ( ~ r1_binop_1(X13,X14,X15)
        | ~ r2_binop_1(X13,X14,X15)
        | r3_binop_1(X13,X14,X15)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13)))
        | ~ m1_subset_1(X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r2_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v3_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
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

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ r2_binop_1(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r1_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] :
      ( ( v1_funct_1(X26)
        | ~ m2_filter_1(X26,X24,X25)
        | v1_xboole_0(X24)
        | ~ v1_relat_1(X25) )
      & ( v1_funct_2(X26,k2_zfmisc_1(X24,X24),X24)
        | ~ m2_filter_1(X26,X24,X25)
        | v1_xboole_0(X24)
        | ~ v1_relat_1(X25) )
      & ( m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))
        | ~ m2_filter_1(X26,X24,X25)
        | v1_xboole_0(X24)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ r2_binop_1(esk1_0,X1,X2)
    | ~ r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ v1_funct_2(k3_filter_1(esk1_0,esk2_0,X2),k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m1_subset_1(k3_filter_1(esk1_0,esk2_0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ r1_binop_1(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_32,plain,(
    ! [X16,X17,X18] :
      ( ( v1_funct_1(k3_filter_1(X16,X17,X18))
        | v1_xboole_0(X16)
        | ~ v1_partfun1(X17,X16)
        | ~ v3_relat_2(X17)
        | ~ v8_relat_2(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))) )
      & ( v1_funct_2(k3_filter_1(X16,X17,X18),k2_zfmisc_1(k8_eqrel_1(X16,X17),k8_eqrel_1(X16,X17)),k8_eqrel_1(X16,X17))
        | v1_xboole_0(X16)
        | ~ v1_partfun1(X17,X16)
        | ~ v3_relat_2(X17)
        | ~ v8_relat_2(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))) )
      & ( m1_subset_1(k3_filter_1(X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X16,X17),k8_eqrel_1(X16,X17)),k8_eqrel_1(X16,X17))))
        | v1_xboole_0(X16)
        | ~ v1_partfun1(X17,X16)
        | ~ v3_relat_2(X17)
        | ~ v8_relat_2(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( m2_filter_1(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
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

fof(c_0_39,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_40,plain,(
    ! [X19,X20] :
      ( ~ v3_relat_2(X20)
      | ~ v8_relat_2(X20)
      | ~ v1_partfun1(X20,X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19)))
      | m1_subset_1(k7_eqrel_1(X19,X20),k1_zfmisc_1(k1_zfmisc_1(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_eqrel_1])])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ~ v3_relat_2(X30)
      | ~ v8_relat_2(X30)
      | ~ v1_partfun1(X30,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29)))
      | k8_eqrel_1(X29,X30) = k7_eqrel_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_eqrel_1])])).

fof(c_0_42,plain,(
    ! [X27,X28] :
      ( v1_xboole_0(X27)
      | ~ v3_relat_2(X28)
      | ~ v8_relat_2(X28)
      | ~ v1_partfun1(X28,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))
      | ~ v1_xboole_0(k7_eqrel_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_eqrel_1])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m2_filter_1(X2,esk1_0,esk2_0)
    | ~ r2_binop_1(esk1_0,X1,X2)
    | ~ r1_binop_1(esk1_0,X1,X2)
    | ~ v1_funct_2(k3_filter_1(esk1_0,esk2_0,X2),k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k3_filter_1(esk1_0,esk2_0,X2))
    | ~ m1_subset_1(k3_filter_1(esk1_0,esk2_0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_35])]),c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_35])]),c_0_22])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( m1_subset_1(k7_eqrel_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k8_eqrel_1(X2,X1) = k7_eqrel_1(X2,X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_54,plain,(
    ! [X21,X22,X23] :
      ( v1_xboole_0(X21)
      | ~ v3_relat_2(X22)
      | ~ v8_relat_2(X22)
      | ~ v1_partfun1(X22,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21)))
      | ~ m1_subset_1(X23,X21)
      | m2_subset_1(k9_eqrel_1(X21,X22,X23),k1_zfmisc_1(X21),k8_eqrel_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_xboole_0(k7_eqrel_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ v1_funct_2(k3_filter_1(esk1_0,esk2_0,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_subset_1(k3_filter_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34]),c_0_45])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])]),c_0_22])).

cnf(c_0_58,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ m2_subset_1(X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(k7_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_subset_1(k3_filter_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))
    | ~ m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_19]),c_0_20]),c_0_21]),c_0_18])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k3_filter_1(esk1_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_48]),c_0_49])]),c_0_22])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k8_eqrel_1(X2,X3))
    | v1_xboole_0(k8_eqrel_1(X2,X3))
    | ~ v8_relat_2(X3)
    | ~ v3_relat_2(X3)
    | ~ v1_partfun1(X3,X2)
    | ~ m2_subset_1(X1,k1_zfmisc_1(X2),k8_eqrel_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( m2_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k1_zfmisc_1(esk1_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_53]),c_0_19]),c_0_20]),c_0_21]),c_0_18])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))
    | ~ m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_19]),c_0_20]),c_0_21]),c_0_18])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_19]),c_0_20]),c_0_21]),c_0_18])]),c_0_67])).

cnf(c_0_70,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_45])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk1_0,X1,esk4_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_47]),c_0_48]),c_0_49])]),c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_19]),c_0_20]),c_0_21]),c_0_18])])).

cnf(c_0_74,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_48]),c_0_49]),c_0_47]),c_0_45])])).

cnf(c_0_77,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_75]),c_0_48]),c_0_49]),c_0_47]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:51:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.12/0.37  # and selection function PSelectComplexExceptRRHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.030 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t8_filter_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r3_binop_1(X1,X3,X4)=>r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_filter_1)).
% 0.12/0.37  fof(t7_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r2_binop_1(X1,X3,X4)=>r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_filter_1)).
% 0.12/0.37  fof(d7_binop_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>(r3_binop_1(X1,X2,X3)<=>(r1_binop_1(X1,X2,X3)&r2_binop_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_binop_1)).
% 0.12/0.37  fof(t6_filter_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r1_binop_1(X1,X3,X4)=>r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_filter_1)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(dt_m2_filter_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_relat_1(X2))=>![X3]:(m2_filter_1(X3,X1,X2)=>((v1_funct_1(X3)&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 0.12/0.37  fof(dt_k3_filter_1, axiom, ![X1, X2, X3]:((((((((~(v1_xboole_0(X1))&v1_partfun1(X2,X1))&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))&v1_funct_1(X3))&v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))))=>((v1_funct_1(k3_filter_1(X1,X2,X3))&v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))&m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 0.12/0.37  fof(redefinition_m2_subset_1, axiom, ![X1, X2]:(((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(X1)))=>![X3]:(m2_subset_1(X3,X1,X2)<=>m1_subset_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 0.12/0.37  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.12/0.37  fof(dt_k7_eqrel_1, axiom, ![X1, X2]:((((v3_relat_2(X2)&v8_relat_2(X2))&v1_partfun1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>m1_subset_1(k7_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_eqrel_1)).
% 0.12/0.37  fof(redefinition_k8_eqrel_1, axiom, ![X1, X2]:((((v3_relat_2(X2)&v8_relat_2(X2))&v1_partfun1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k8_eqrel_1(X1,X2)=k7_eqrel_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_eqrel_1)).
% 0.12/0.37  fof(fc3_eqrel_1, axiom, ![X1, X2]:(((((~(v1_xboole_0(X1))&v3_relat_2(X2))&v8_relat_2(X2))&v1_partfun1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>~(v1_xboole_0(k7_eqrel_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_eqrel_1)).
% 0.12/0.37  fof(dt_k9_eqrel_1, axiom, ![X1, X2, X3]:((((((~(v1_xboole_0(X1))&v3_relat_2(X2))&v8_relat_2(X2))&v1_partfun1(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))&m1_subset_1(X3,X1))=>m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 0.12/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((((v1_partfun1(X2,X1)&v3_relat_2(X2))&v8_relat_2(X2))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m2_filter_1(X4,X1,X2)=>(r3_binop_1(X1,X3,X4)=>r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4)))))))), inference(assume_negation,[status(cth)],[t8_filter_1])).
% 0.12/0.37  fof(c_0_14, plain, ![X35, X36, X37, X38]:(v1_xboole_0(X35)|(~v1_partfun1(X36,X35)|~v3_relat_2(X36)|~v8_relat_2(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35)))|(~m1_subset_1(X37,X35)|(~m2_filter_1(X38,X35,X36)|(~r2_binop_1(X35,X37,X38)|r2_binop_1(k8_eqrel_1(X35,X36),k9_eqrel_1(X35,X36,X37),k3_filter_1(X35,X36,X38))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_filter_1])])])])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, (~v1_xboole_0(esk1_0)&((((v1_partfun1(esk2_0,esk1_0)&v3_relat_2(esk2_0))&v8_relat_2(esk2_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(m1_subset_1(esk3_0,esk1_0)&(m2_filter_1(esk4_0,esk1_0,esk2_0)&(r3_binop_1(esk1_0,esk3_0,esk4_0)&~r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.12/0.37  fof(c_0_16, plain, ![X13, X14, X15]:(((r1_binop_1(X13,X14,X15)|~r3_binop_1(X13,X14,X15)|(~v1_funct_1(X15)|~v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13))))|~m1_subset_1(X14,X13))&(r2_binop_1(X13,X14,X15)|~r3_binop_1(X13,X14,X15)|(~v1_funct_1(X15)|~v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13))))|~m1_subset_1(X14,X13)))&(~r1_binop_1(X13,X14,X15)|~r2_binop_1(X13,X14,X15)|r3_binop_1(X13,X14,X15)|(~v1_funct_1(X15)|~v1_funct_2(X15,k2_zfmisc_1(X13,X13),X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X13),X13))))|~m1_subset_1(X14,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).
% 0.12/0.37  cnf(c_0_17, plain, (v1_xboole_0(X1)|r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,X1)|~m2_filter_1(X4,X1,X2)|~r2_binop_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v8_relat_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v3_relat_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v1_partfun1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  fof(c_0_23, plain, ![X31, X32, X33, X34]:(v1_xboole_0(X31)|(~v1_partfun1(X32,X31)|~v3_relat_2(X32)|~v8_relat_2(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X31)))|(~m1_subset_1(X33,X31)|(~m2_filter_1(X34,X31,X32)|(~r1_binop_1(X31,X33,X34)|r1_binop_1(k8_eqrel_1(X31,X32),k9_eqrel_1(X31,X32,X33),k3_filter_1(X31,X32,X34))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_filter_1])])])])).
% 0.12/0.37  fof(c_0_24, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|v1_relat_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  cnf(c_0_25, plain, (r3_binop_1(X1,X2,X3)|~r1_binop_1(X1,X2,X3)|~r2_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (r2_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~r2_binop_1(esk1_0,X1,X2)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.12/0.37  cnf(c_0_27, plain, (v1_xboole_0(X1)|r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,X1)|~m2_filter_1(X4,X1,X2)|~r1_binop_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  fof(c_0_28, plain, ![X24, X25, X26]:(((v1_funct_1(X26)|~m2_filter_1(X26,X24,X25)|(v1_xboole_0(X24)|~v1_relat_1(X25)))&(v1_funct_2(X26,k2_zfmisc_1(X24,X24),X24)|~m2_filter_1(X26,X24,X25)|(v1_xboole_0(X24)|~v1_relat_1(X25))))&(m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X24,X24),X24)))|~m2_filter_1(X26,X24,X25)|(v1_xboole_0(X24)|~v1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).
% 0.12/0.37  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~r2_binop_1(esk1_0,X1,X2)|~r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~v1_funct_2(k3_filter_1(esk1_0,esk2_0,X2),k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))|~v1_funct_1(k3_filter_1(esk1_0,esk2_0,X2))|~m1_subset_1(k3_filter_1(esk1_0,esk2_0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))|~m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r1_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~r1_binop_1(esk1_0,X1,X2)|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.12/0.37  fof(c_0_32, plain, ![X16, X17, X18]:(((v1_funct_1(k3_filter_1(X16,X17,X18))|(v1_xboole_0(X16)|~v1_partfun1(X17,X16)|~v3_relat_2(X17)|~v8_relat_2(X17)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))|~v1_funct_1(X18)|~v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))))&(v1_funct_2(k3_filter_1(X16,X17,X18),k2_zfmisc_1(k8_eqrel_1(X16,X17),k8_eqrel_1(X16,X17)),k8_eqrel_1(X16,X17))|(v1_xboole_0(X16)|~v1_partfun1(X17,X16)|~v3_relat_2(X17)|~v8_relat_2(X17)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))|~v1_funct_1(X18)|~v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))))))&(m1_subset_1(k3_filter_1(X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X16,X17),k8_eqrel_1(X16,X17)),k8_eqrel_1(X16,X17))))|(v1_xboole_0(X16)|~v1_partfun1(X17,X16)|~v3_relat_2(X17)|~v8_relat_2(X17)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))|~v1_funct_1(X18)|~v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).
% 0.12/0.37  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (m2_filter_1(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 0.12/0.37  cnf(c_0_36, plain, (v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_37, plain, (v1_funct_1(X1)|v1_xboole_0(X2)|~m2_filter_1(X1,X2,X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  fof(c_0_38, plain, ![X10, X11, X12]:((~m2_subset_1(X12,X10,X11)|m1_subset_1(X12,X11)|(v1_xboole_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(X10))))&(~m1_subset_1(X12,X11)|m2_subset_1(X12,X10,X11)|(v1_xboole_0(X10)|v1_xboole_0(X11)|~m1_subset_1(X11,k1_zfmisc_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).
% 0.12/0.37  fof(c_0_39, plain, ![X5, X6]:(~v1_xboole_0(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.12/0.37  fof(c_0_40, plain, ![X19, X20]:(~v3_relat_2(X20)|~v8_relat_2(X20)|~v1_partfun1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19)))|m1_subset_1(k7_eqrel_1(X19,X20),k1_zfmisc_1(k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_eqrel_1])])).
% 0.12/0.37  fof(c_0_41, plain, ![X29, X30]:(~v3_relat_2(X30)|~v8_relat_2(X30)|~v1_partfun1(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29)))|k8_eqrel_1(X29,X30)=k7_eqrel_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_eqrel_1])])).
% 0.12/0.37  fof(c_0_42, plain, ![X27, X28]:(v1_xboole_0(X27)|~v3_relat_2(X28)|~v8_relat_2(X28)|~v1_partfun1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X27)))|~v1_xboole_0(k7_eqrel_1(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_eqrel_1])])])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (~r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,X1),k3_filter_1(esk1_0,esk2_0,X2))|~m2_filter_1(X2,esk1_0,esk2_0)|~r2_binop_1(esk1_0,X1,X2)|~r1_binop_1(esk1_0,X1,X2)|~v1_funct_2(k3_filter_1(esk1_0,esk2_0,X2),k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))|~v1_funct_1(k3_filter_1(esk1_0,esk2_0,X2))|~m1_subset_1(k3_filter_1(esk1_0,esk2_0,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))|~m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_46, plain, (v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), c_0_22])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34]), c_0_35])]), c_0_22])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_35])]), c_0_22])).
% 0.12/0.37  cnf(c_0_50, plain, (m1_subset_1(X1,X3)|v1_xboole_0(X2)|v1_xboole_0(X3)|~m2_subset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_51, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_52, plain, (m1_subset_1(k7_eqrel_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~v3_relat_2(X1)|~v8_relat_2(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_53, plain, (k8_eqrel_1(X2,X1)=k7_eqrel_1(X2,X1)|~v3_relat_2(X1)|~v8_relat_2(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.37  fof(c_0_54, plain, ![X21, X22, X23]:(v1_xboole_0(X21)|~v3_relat_2(X22)|~v8_relat_2(X22)|~v1_partfun1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21)))|~m1_subset_1(X23,X21)|m2_subset_1(k9_eqrel_1(X21,X22,X23),k1_zfmisc_1(X21),k8_eqrel_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).
% 0.12/0.37  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~v1_partfun1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_xboole_0(k7_eqrel_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk4_0)|~r1_binop_1(esk1_0,esk3_0,esk4_0)|~v1_funct_2(k3_filter_1(esk1_0,esk2_0,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))|~v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))|~m1_subset_1(k3_filter_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))|~m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34]), c_0_45])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (v1_funct_2(k3_filter_1(esk1_0,X1,esk4_0),k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])]), c_0_22])).
% 0.12/0.37  cnf(c_0_58, plain, (m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_59, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~m2_subset_1(X1,X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.37  cnf(c_0_60, plain, (m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))|~v8_relat_2(X2)|~v3_relat_2(X2)|~v1_partfun1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.37  cnf(c_0_61, plain, (v1_xboole_0(X1)|m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))|~v3_relat_2(X2)|~v8_relat_2(X2)|~v1_partfun1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(k7_eqrel_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk4_0)|~r1_binop_1(esk1_0,esk3_0,esk4_0)|~v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))|~m1_subset_1(k3_filter_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,esk2_0),k8_eqrel_1(esk1_0,esk2_0)),k8_eqrel_1(esk1_0,esk2_0))))|~m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_19]), c_0_20]), c_0_21]), c_0_18])])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (m1_subset_1(k3_filter_1(esk1_0,X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk1_0,X1),k8_eqrel_1(esk1_0,X1)),k8_eqrel_1(esk1_0,X1))))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_47]), c_0_48]), c_0_49])]), c_0_22])).
% 0.12/0.37  cnf(c_0_65, plain, (m1_subset_1(X1,k8_eqrel_1(X2,X3))|v1_xboole_0(k8_eqrel_1(X2,X3))|~v8_relat_2(X3)|~v3_relat_2(X3)|~v1_partfun1(X3,X2)|~m2_subset_1(X1,k1_zfmisc_1(X2),k8_eqrel_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (m2_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k1_zfmisc_1(esk1_0),k8_eqrel_1(esk1_0,esk2_0))|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (~v1_xboole_0(k8_eqrel_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_53]), c_0_19]), c_0_20]), c_0_21]), c_0_18])])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk4_0)|~r1_binop_1(esk1_0,esk3_0,esk4_0)|~v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))|~m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_19]), c_0_20]), c_0_21]), c_0_18])])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_19]), c_0_20]), c_0_21]), c_0_18])]), c_0_67])).
% 0.12/0.37  cnf(c_0_70, plain, (v1_funct_1(k3_filter_1(X1,X2,X3))|v1_xboole_0(X1)|~v1_partfun1(X2,X1)|~v3_relat_2(X2)|~v8_relat_2(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk4_0)|~r1_binop_1(esk1_0,esk3_0,esk4_0)|~v1_funct_1(k3_filter_1(esk1_0,esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_45])])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (v1_funct_1(k3_filter_1(esk1_0,X1,esk4_0))|~v8_relat_2(X1)|~v3_relat_2(X1)|~v1_partfun1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_47]), c_0_48]), c_0_49])]), c_0_22])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (~r2_binop_1(esk1_0,esk3_0,esk4_0)|~r1_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_19]), c_0_20]), c_0_21]), c_0_18])])).
% 0.12/0.37  cnf(c_0_74, plain, (r2_binop_1(X1,X2,X3)|~r3_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_75, negated_conjecture, (r3_binop_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (~r1_binop_1(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_48]), c_0_49]), c_0_47]), c_0_45])])).
% 0.12/0.37  cnf(c_0_77, plain, (r1_binop_1(X1,X2,X3)|~r3_binop_1(X1,X2,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_75]), c_0_48]), c_0_49]), c_0_47]), c_0_45])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 79
% 0.12/0.37  # Proof object clause steps            : 52
% 0.12/0.37  # Proof object formula steps           : 27
% 0.12/0.37  # Proof object conjectures             : 34
% 0.12/0.37  # Proof object clause conjectures      : 31
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 27
% 0.12/0.37  # Proof object initial formulas used   : 13
% 0.12/0.37  # Proof object generating inferences   : 24
% 0.12/0.37  # Proof object simplifying inferences  : 85
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 13
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 28
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 28
% 0.12/0.37  # Processed clauses                    : 99
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 97
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 4
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 57
% 0.12/0.37  # ...of the previous two non-trivial   : 53
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 57
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 65
% 0.12/0.37  #    Positive orientable unit clauses  : 12
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 6
% 0.12/0.37  #    Non-unit-clauses                  : 47
% 0.12/0.37  # Current number of unprocessed clauses: 10
% 0.12/0.37  # ...number of literals in the above   : 92
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 32
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 1583
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 132
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.37  # Unit Clause-clause subsumption calls : 78
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 6375
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.036 s
% 0.12/0.37  # System time              : 0.007 s
% 0.12/0.37  # Total time               : 0.043 s
% 0.12/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
