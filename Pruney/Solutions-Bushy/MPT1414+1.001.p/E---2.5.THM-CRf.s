%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1414+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 656 expanded)
%              Number of clauses        :   59 ( 221 expanded)
%              Number of leaves         :   16 ( 162 expanded)
%              Depth                    :   11
%              Number of atoms          :  409 (4077 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   27 (   3 average)
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

fof(redefinition_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k8_eqrel_1(X1,X2) = k7_eqrel_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

fof(dt_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_eqrel_1(k8_eqrel_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

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

fof(dt_k7_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_subset_1(k7_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

fof(cc1_eqrel_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_eqrel_1(X2,X1)
         => ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_eqrel_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_partfun1(esk3_0,esk2_0)
    & v3_relat_2(esk3_0)
    & v8_relat_2(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & m1_subset_1(esk4_0,esk2_0)
    & m2_filter_1(esk5_0,esk2_0,esk3_0)
    & r3_binop_1(esk2_0,esk4_0,esk5_0)
    & ~ r3_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,esk4_0),k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
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

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] :
      ( v1_xboole_0(X20)
      | ~ v3_relat_2(X21)
      | ~ v8_relat_2(X21)
      | ~ v1_partfun1(X21,X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X20)))
      | ~ m1_subset_1(X22,X20)
      | m2_subset_1(k9_eqrel_1(X20,X21,X22),k1_zfmisc_1(X20),k8_eqrel_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

fof(c_0_23,plain,(
    ! [X28,X29] :
      ( ~ v3_relat_2(X29)
      | ~ v8_relat_2(X29)
      | ~ v1_partfun1(X29,X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))
      | k8_eqrel_1(X28,X29) = k7_eqrel_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_eqrel_1])])).

fof(c_0_24,plain,(
    ! [X18,X19] :
      ( ~ v3_relat_2(X19)
      | ~ v8_relat_2(X19)
      | ~ v1_partfun1(X19,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X18)))
      | m1_eqrel_1(k8_eqrel_1(X18,X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).

fof(c_0_25,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_26,plain,(
    ! [X26] : m1_subset_1(esk1_1(X26),X26) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m2_filter_1(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( v1_partfun1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( v8_relat_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( v3_relat_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X16,X17] :
      ( ~ v3_relat_2(X17)
      | ~ v8_relat_2(X17)
      | ~ v1_partfun1(X17,X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X16)))
      | m1_subset_1(k7_eqrel_1(X16,X17),k1_zfmisc_1(k1_zfmisc_1(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_eqrel_1])])).

cnf(c_0_39,plain,
    ( k8_eqrel_1(X2,X1) = k7_eqrel_1(X2,X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_40,plain,(
    ! [X5,X6] :
      ( v1_xboole_0(X5)
      | ~ m1_eqrel_1(X6,X5)
      | ~ v1_xboole_0(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).

cnf(c_0_41,plain,
    ( m1_eqrel_1(k8_eqrel_1(X2,X1),X2)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_42,plain,(
    ! [X38,X39,X40] :
      ( ~ r2_hidden(X38,X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(X40))
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_45,plain,(
    ! [X45,X46,X47,X48] :
      ( v1_xboole_0(X45)
      | ~ v1_partfun1(X46,X45)
      | ~ v3_relat_2(X46)
      | ~ v8_relat_2(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X45)))
      | ~ m1_subset_1(X47,X45)
      | ~ m2_filter_1(X48,X45,X46)
      | ~ r2_binop_1(X45,X47,X48)
      | r2_binop_1(k8_eqrel_1(X45,X46),k9_eqrel_1(X45,X46,X47),k3_filter_1(X45,X46,X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_filter_1])])])])).

cnf(c_0_46,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r3_binop_1(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_52,plain,(
    ! [X41,X42,X43,X44] :
      ( v1_xboole_0(X41)
      | ~ v1_partfun1(X42,X41)
      | ~ v3_relat_2(X42)
      | ~ v8_relat_2(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X41)))
      | ~ m1_subset_1(X43,X41)
      | ~ m2_filter_1(X44,X41,X42)
      | ~ r1_binop_1(X41,X43,X44)
      | r1_binop_1(k8_eqrel_1(X41,X42),k9_eqrel_1(X41,X42,X43),k3_filter_1(X41,X42,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_filter_1])])])])).

cnf(c_0_53,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_54,plain,(
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

fof(c_0_55,plain,(
    ! [X33,X34,X35] :
      ( ( ~ m2_subset_1(X35,X33,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) )
      & ( ~ m1_subset_1(X35,X34)
        | m2_subset_1(X35,X33,X34)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

cnf(c_0_56,negated_conjecture,
    ( m2_subset_1(k9_eqrel_1(esk2_0,esk3_0,X1),k1_zfmisc_1(esk2_0),k8_eqrel_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_21])]),c_0_31])).

cnf(c_0_57,plain,
    ( m1_subset_1(k7_eqrel_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_58,negated_conjecture,
    ( k7_eqrel_1(esk2_0,esk3_0) = k8_eqrel_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_36]),c_0_37]),c_0_21])])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | ~ m1_eqrel_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( m1_eqrel_1(k8_eqrel_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_36]),c_0_37]),c_0_21])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r2_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( r2_binop_1(esk2_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X1)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r1_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( r1_binop_1(esk2_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_67,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( m2_subset_1(k9_eqrel_1(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(esk2_0),k8_eqrel_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k8_eqrel_1(esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_58]),c_0_36]),c_0_37]),c_0_21])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_31])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r2_binop_1(k8_eqrel_1(esk2_0,X1),k9_eqrel_1(esk2_0,X1,esk4_0),k3_filter_1(esk2_0,X1,esk5_0))
    | ~ m2_filter_1(esk5_0,esk2_0,X1)
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_51])]),c_0_31])).

cnf(c_0_74,negated_conjecture,
    ( r1_binop_1(k8_eqrel_1(esk2_0,X1),k9_eqrel_1(esk2_0,X1,esk4_0),k3_filter_1(esk2_0,X1,esk5_0))
    | ~ m2_filter_1(esk5_0,esk2_0,X1)
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_51])]),c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk2_0,X1,esk5_0))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_48]),c_0_49]),c_0_50])]),c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k9_eqrel_1(esk2_0,esk3_0,esk4_0),k8_eqrel_1(esk2_0,esk3_0))
    | v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_70]),c_0_71])).

cnf(c_0_78,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_79,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_80,negated_conjecture,
    ( r2_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,esk4_0),k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_29]),c_0_36]),c_0_37]),c_0_35]),c_0_21])])).

cnf(c_0_81,negated_conjecture,
    ( r1_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,esk4_0),k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_29]),c_0_36]),c_0_37]),c_0_35]),c_0_21])])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_35]),c_0_36]),c_0_37]),c_0_21])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k9_eqrel_1(esk2_0,esk3_0,esk4_0),k8_eqrel_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(esk2_0,esk3_0),k9_eqrel_1(esk2_0,esk3_0,esk4_0),k3_filter_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk2_0,X1,esk5_0),k2_zfmisc_1(k8_eqrel_1(esk2_0,X1),k8_eqrel_1(esk2_0,X1)),k8_eqrel_1(esk2_0,X1))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_48]),c_0_49]),c_0_50])]),c_0_31])).

cnf(c_0_86,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_funct_2(k3_filter_1(esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k8_eqrel_1(esk2_0,esk3_0),k8_eqrel_1(esk2_0,esk3_0)),k8_eqrel_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k3_filter_1(esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk2_0,esk3_0),k8_eqrel_1(esk2_0,esk3_0)),k8_eqrel_1(esk2_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_82]),c_0_83])]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(k3_filter_1(esk2_0,esk3_0,esk5_0),k2_zfmisc_1(k8_eqrel_1(esk2_0,esk3_0),k8_eqrel_1(esk2_0,esk3_0)),k8_eqrel_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_35]),c_0_36]),c_0_37]),c_0_21])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k3_filter_1(esk2_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk2_0,X1),k8_eqrel_1(esk2_0,X1)),k8_eqrel_1(esk2_0,X1))))
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_48]),c_0_49]),c_0_50])]),c_0_31])).

cnf(c_0_90,negated_conjecture,
    ( ~ m1_subset_1(k3_filter_1(esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(esk2_0,esk3_0),k8_eqrel_1(esk2_0,esk3_0)),k8_eqrel_1(esk2_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_35]),c_0_36]),c_0_37]),c_0_21])]),c_0_90]),
    [proof]).

%------------------------------------------------------------------------------
