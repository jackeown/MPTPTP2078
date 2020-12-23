%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t8_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 151.50s
% Output     : CNFRefutation 151.50s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 389 expanded)
%              Number of clauses        :   54 ( 137 expanded)
%              Number of leaves         :   17 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  449 (2444 expanded)
%              Number of equality atoms :    4 (   4 expanded)
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',t8_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',d7_binop_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',dt_k3_filter_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',t5_subset)).

fof(dt_k7_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_subset_1(k7_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',dt_k7_eqrel_1)).

fof(redefinition_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k8_eqrel_1(X1,X2) = k7_eqrel_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',redefinition_k8_eqrel_1)).

fof(cc1_eqrel_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_eqrel_1(X2,X1)
         => ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',cc1_eqrel_1)).

fof(dt_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_eqrel_1(k8_eqrel_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',dt_k8_eqrel_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',t7_filter_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',cc1_relset_1)).

fof(dt_m2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2) )
     => ! [X3] :
          ( m2_filter_1(X3,X1,X2)
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',dt_m2_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',t6_filter_1)).

fof(dt_m1_eqrel_1,axiom,(
    ! [X1,X2] :
      ( m1_eqrel_1(X2,X1)
     => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',dt_m1_eqrel_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',t2_subset)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',redefinition_m2_subset_1)).

fof(dt_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',dt_k9_eqrel_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t8_filter_1.p',existence_m1_subset_1)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X16,X17,X18] :
      ( ( r1_binop_1(X16,X17,X18)
        | ~ r3_binop_1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))
        | ~ m1_subset_1(X17,X16) )
      & ( r2_binop_1(X16,X17,X18)
        | ~ r3_binop_1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))
        | ~ m1_subset_1(X17,X16) )
      & ( ~ r1_binop_1(X16,X17,X18)
        | ~ r2_binop_1(X16,X17,X18)
        | r3_binop_1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,k2_zfmisc_1(X16,X16),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X16,X16),X16)))
        | ~ m1_subset_1(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_binop_1])])])])).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X65,X66,X67] :
      ( ~ r2_hidden(X65,X66)
      | ~ m1_subset_1(X66,k1_zfmisc_1(X67))
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ~ v3_relat_2(X23)
      | ~ v8_relat_2(X23)
      | ~ v1_partfun1(X23,X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
      | m1_subset_1(k7_eqrel_1(X22,X23),k1_zfmisc_1(k1_zfmisc_1(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_eqrel_1])])).

fof(c_0_22,plain,(
    ! [X48,X49] :
      ( ~ v3_relat_2(X49)
      | ~ v8_relat_2(X49)
      | ~ v1_partfun1(X49,X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X48)))
      | k8_eqrel_1(X48,X49) = k7_eqrel_1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_eqrel_1])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_partfun1(esk2_0,esk1_0)
    & v3_relat_2(esk2_0)
    & v8_relat_2(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & m1_subset_1(esk3_0,esk1_0)
    & m2_filter_1(esk4_0,esk1_0,esk2_0)
    & r3_binop_1(esk1_0,esk3_0,esk4_0)
    & ~ r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( v1_xboole_0(X11)
      | ~ m1_eqrel_1(X12,X11)
      | ~ v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).

fof(c_0_25,plain,(
    ! [X24,X25] :
      ( ~ v3_relat_2(X25)
      | ~ v8_relat_2(X25)
      | ~ v1_partfun1(X25,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X24,X24)))
      | m1_eqrel_1(k8_eqrel_1(X24,X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).

cnf(c_0_26,plain,
    ( r3_binop_1(X1,X2,X3)
    | ~ r1_binop_1(X1,X2,X3)
    | ~ r2_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X75,X76,X77,X78] :
      ( v1_xboole_0(X75)
      | ~ v1_partfun1(X76,X75)
      | ~ v3_relat_2(X76)
      | ~ v8_relat_2(X76)
      | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X75,X75)))
      | ~ m1_subset_1(X77,X75)
      | ~ m2_filter_1(X78,X75,X76)
      | ~ r2_binop_1(X75,X77,X78)
      | r2_binop_1(k8_eqrel_1(X75,X76),k9_eqrel_1(X75,X76,X77),k3_filter_1(X75,X76,X78)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_filter_1])])])])).

fof(c_0_31,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_32,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ m2_filter_1(X33,X31,X32)
        | v1_xboole_0(X31)
        | ~ v1_relat_1(X32) )
      & ( v1_funct_2(X33,k2_zfmisc_1(X31,X31),X31)
        | ~ m2_filter_1(X33,X31,X32)
        | v1_xboole_0(X31)
        | ~ v1_relat_1(X32) )
      & ( m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X31,X31),X31)))
        | ~ m2_filter_1(X33,X31,X32)
        | v1_xboole_0(X31)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( m1_subset_1(k7_eqrel_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k8_eqrel_1(X2,X1) = k7_eqrel_1(X2,X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v3_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | ~ m1_eqrel_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( m1_eqrel_1(k8_eqrel_1(X2,X1),X2)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( r3_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r2_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X4))
    | ~ r1_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X4))
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,k8_eqrel_1(X1,X2))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | r2_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r2_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_44,plain,(
    ! [X69,X70,X71,X72] :
      ( v1_xboole_0(X69)
      | ~ v1_partfun1(X70,X69)
      | ~ v3_relat_2(X70)
      | ~ v8_relat_2(X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X69)))
      | ~ m1_subset_1(X71,X69)
      | ~ m2_filter_1(X72,X69,X70)
      | ~ r1_binop_1(X69,X71,X72)
      | r1_binop_1(k8_eqrel_1(X69,X70),k9_eqrel_1(X69,X70,X71),k3_filter_1(X69,X70,X72)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_filter_1])])])])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( m2_filter_1(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_49,plain,(
    ! [X29,X30] :
      ( ~ m1_eqrel_1(X30,X29)
      | m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_eqrel_1])])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k7_eqrel_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v8_relat_2(X3)
    | ~ v3_relat_2(X3)
    | ~ v1_partfun1(X3,X2)
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( k7_eqrel_1(esk1_0,esk2_0) = k8_eqrel_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

fof(c_0_52,plain,(
    ! [X58,X59] :
      ( ~ m1_subset_1(X58,X59)
      | v1_xboole_0(X59)
      | r2_hidden(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r2_binop_1(X1,X3,X4)
    | ~ r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(k9_eqrel_1(X1,X2,X3),k8_eqrel_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | r1_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ r1_binop_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk4_0)
    | ~ v1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_60,plain,(
    ! [X53,X54,X55] :
      ( ( ~ m2_subset_1(X55,X53,X54)
        | m1_subset_1(X55,X54)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53)) )
      & ( ~ m1_subset_1(X55,X54)
        | m2_subset_1(X55,X53,X54)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

fof(c_0_61,plain,(
    ! [X26,X27,X28] :
      ( v1_xboole_0(X26)
      | ~ v3_relat_2(X27)
      | ~ v8_relat_2(X27)
      | ~ v1_partfun1(X27,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26)))
      | ~ m1_subset_1(X28,X26)
      | m2_subset_1(k9_eqrel_1(X26,X27,X28),k1_zfmisc_1(X26),k8_eqrel_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_eqrel_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,k8_eqrel_1(esk1_0,esk2_0))
    | ~ v1_xboole_0(k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_51]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_48])).

fof(c_0_66,plain,(
    ! [X39] : m1_subset_1(esk6_1(X39),X39) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r3_binop_1(k8_eqrel_1(esk1_0,esk2_0),k9_eqrel_1(esk1_0,esk2_0,esk3_0),k3_filter_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_68,plain,
    ( r3_binop_1(k8_eqrel_1(X1,X2),k9_eqrel_1(X1,X2,X3),k3_filter_1(X1,X2,X4))
    | v1_xboole_0(X1)
    | ~ r2_binop_1(X1,X3,X4)
    | ~ r1_binop_1(X1,X3,X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X4)
    | ~ m2_filter_1(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(k9_eqrel_1(X1,X2,X3),k8_eqrel_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_47]),c_0_48]),c_0_57])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_57])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_48]),c_0_57])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,plain,
    ( m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(X1,k8_eqrel_1(esk1_0,esk2_0))
    | ~ v1_xboole_0(k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k9_eqrel_1(esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70]),c_0_47]),c_0_71]),c_0_36]),c_0_72]),c_0_37]),c_0_38]),c_0_39])]),c_0_48])).

cnf(c_0_79,plain,
    ( m1_subset_1(k9_eqrel_1(X1,X2,X3),k8_eqrel_1(X1,X2))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_53])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,plain,
    ( r2_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_binop_1(esk1_0,esk3_0,esk4_0)
    | ~ r1_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_36]),c_0_72]),c_0_37]),c_0_38]),c_0_39])]),c_0_80]),c_0_48])).

cnf(c_0_83,negated_conjecture,
    ( r2_binop_1(esk1_0,X1,esk4_0)
    | ~ r3_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_69]),c_0_70]),c_0_71])])).

cnf(c_0_84,negated_conjecture,
    ( r3_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,plain,
    ( r1_binop_1(X1,X2,X3)
    | ~ r3_binop_1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_binop_1(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_72])])).

cnf(c_0_87,negated_conjecture,
    ( r1_binop_1(esk1_0,X1,esk4_0)
    | ~ r3_binop_1(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_69]),c_0_70]),c_0_71])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_84]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
