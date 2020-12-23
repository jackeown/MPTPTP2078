%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t11_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:06 EDT 2019

% Result     : Theorem 151.39s
% Output     : CNFRefutation 151.39s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 442 expanded)
%              Number of clauses        :   37 ( 156 expanded)
%              Number of leaves         :    7 ( 111 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 (2869 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   27 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',d11_binop_1)).

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
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_k3_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t11_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t10_filter_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t9_filter_1)).

fof(dt_m2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2) )
     => ! [X3] :
          ( m2_filter_1(X3,X1,X2)
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_m2_filter_1)).

fof(c_0_7,plain,(
    ! [X16,X17,X18] :
      ( ( r4_binop_1(X16,X17,X18)
        | ~ r6_binop_1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))) )
      & ( r5_binop_1(X16,X17,X18)
        | ~ r6_binop_1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))) )
      & ( ~ r4_binop_1(X16,X17,X18)
        | ~ r5_binop_1(X16,X17,X18)
        | r6_binop_1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_binop_1])])])])).

fof(c_0_8,plain,(
    ! [X19,X20,X21] :
      ( ( v1_funct_1(k3_filter_1(X19,X20,X21))
        | v1_xboole_0(X19)
        | ~ v1_partfun1(X20,X19)
        | ~ v3_relat_2(X20)
        | ~ v8_relat_2(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,k2_zfmisc_1(X19,X19),X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19))) )
      & ( v1_funct_2(k3_filter_1(X19,X20,X21),k2_zfmisc_1(k8_eqrel_1(X19,X20),k8_eqrel_1(X19,X20)),k8_eqrel_1(X19,X20))
        | v1_xboole_0(X19)
        | ~ v1_partfun1(X20,X19)
        | ~ v3_relat_2(X20)
        | ~ v8_relat_2(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,k2_zfmisc_1(X19,X19),X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19))) )
      & ( m1_subset_1(k3_filter_1(X19,X20,X21),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X19,X20),k8_eqrel_1(X19,X20)),k8_eqrel_1(X19,X20))))
        | v1_xboole_0(X19)
        | ~ v1_partfun1(X20,X19)
        | ~ v3_relat_2(X20)
        | ~ v8_relat_2(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X19,X19)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,k2_zfmisc_1(X19,X19),X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X19,X19),X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

cnf(c_0_9,plain,
    ( r6_binop_1(X1,X2,X3)
    | ~ r4_binop_1(X1,X2,X3)
    | ~ r5_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
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

cnf(c_0_14,plain,
    ( r6_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r5_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X4))
    | ~ r4_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X4))
    | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])).

fof(c_0_15,plain,(
    ! [X41,X42,X43,X44] :
      ( v1_xboole_0(X41)
      | ~ v1_partfun1(X42,X41)
      | ~ v3_relat_2(X42)
      | ~ v8_relat_2(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X41)))
      | ~ m2_filter_1(X43,X41,X42)
      | ~ m2_filter_1(X44,X41,X42)
      | ~ r5_binop_1(X41,X43,X44)
      | r5_binop_1(k8_eqrel_1(X41,X42),k3_filter_1(X41,X42,X43),k3_filter_1(X41,X42,X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_filter_1])])])])).

fof(c_0_16,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_partfun1(esk2_0,esk1_0)
    & v3_relat_2(esk2_0)
    & v8_relat_2(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & m2_filter_1(esk3_0,esk1_0,esk2_0)
    & m2_filter_1(esk4_0,esk1_0,esk2_0)
    & r6_binop_1(esk1_0,esk3_0,esk4_0)
    & ~ r6_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | r5_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r5_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X62,X63,X64,X65] :
      ( v1_xboole_0(X62)
      | ~ v1_partfun1(X63,X62)
      | ~ v3_relat_2(X63)
      | ~ v8_relat_2(X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X62,X62)))
      | ~ m2_filter_1(X64,X62,X63)
      | ~ m2_filter_1(X65,X62,X63)
      | ~ r4_binop_1(X62,X64,X65)
      | r4_binop_1(k8_eqrel_1(X62,X63),k3_filter_1(X62,X63,X64),k3_filter_1(X62,X63,X65)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_filter_1])])])])).

fof(c_0_21,plain,(
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

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r5_binop_1(X1,X3,X4)
    | ~ r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | r4_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r4_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m2_filter_1(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m2_filter_1(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ r6_binop_1(k8_eqrel_1(esk1_0,esk2_0),k3_filter_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r6_binop_1(k8_eqrel_1(X1,X2),k3_filter_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r5_binop_1(X1,X3,X4)
    | ~ r4_binop_1(X1,X3,X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk3_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_28]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_28]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( v3_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( r5_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( ~ r5_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r4_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_27]),c_0_30]),c_0_39]),c_0_40]),c_0_23]),c_0_41]),c_0_42]),c_0_43])]),c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( r5_binop_1(esk1_0,X1,esk4_0)
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1)
    | ~ r6_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_39]),c_0_35]),c_0_37])])).

cnf(c_0_47,negated_conjecture,
    ( r6_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,plain,
    ( r4_binop_1(X1,X2,X3)
    | ~ r6_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_49,negated_conjecture,
    ( ~ r4_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36]),c_0_38]),c_0_47]),c_0_40])])).

cnf(c_0_50,negated_conjecture,
    ( r4_binop_1(esk1_0,X1,esk4_0)
    | ~ v1_funct_2(X1,k2_zfmisc_1(esk1_0,esk1_0),esk1_0)
    | ~ v1_funct_1(X1)
    | ~ r6_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_35]),c_0_37])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_36]),c_0_38]),c_0_47]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
