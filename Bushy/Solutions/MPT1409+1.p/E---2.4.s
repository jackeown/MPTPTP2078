%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t3_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 235.78s
% Output     : CNFRefutation 235.78s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 456 expanded)
%              Number of clauses        :   62 ( 169 expanded)
%              Number of leaves         :   21 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  591 (2679 expanded)
%              Number of equality atoms :   32 ( 203 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   88 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_m1_eqrel_1,axiom,(
    ! [X1,X2] :
      ( m1_eqrel_1(X2,X1)
     => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_m1_eqrel_1)).

fof(existence_m1_eqrel_1,axiom,(
    ! [X1] :
    ? [X2] : m1_eqrel_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',existence_m1_eqrel_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t2_subset)).

fof(t3_filter_1,conjecture,(
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
                  ( m1_subset_1(X4,X1)
                 => ! [X5] :
                      ( m2_filter_1(X5,X1,X2)
                     => k1_binop_1(k3_filter_1(X1,X2,X5),k6_eqrel_1(X1,X1,X2,X3),k6_eqrel_1(X1,X1,X2,X4)) = k6_eqrel_1(X1,X1,X2,k4_binop_1(X1,X5,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t3_filter_1)).

fof(cc1_eqrel_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_eqrel_1(X2,X1)
         => ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',cc1_eqrel_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',existence_m1_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',cc1_relset_1)).

fof(d4_filter_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X1)
            & v3_relat_2(X2)
            & v8_relat_2(X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) )
             => ( m2_filter_1(X3,X1,X2)
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2)))) )
                   => ( X4 = k3_filter_1(X1,X2,X3)
                    <=> ! [X5,X6,X7,X8] :
                          ( ( r2_hidden(X5,k8_eqrel_1(X1,X2))
                            & r2_hidden(X6,k8_eqrel_1(X1,X2))
                            & r2_hidden(X7,X5)
                            & r2_hidden(X8,X6) )
                         => k1_binop_1(X4,X5,X6) = k6_eqrel_1(X1,X1,X2,k1_binop_1(X3,X7,X8)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',d4_filter_1)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k3_filter_1)).

fof(t28_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_2(X2)
        & v3_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,k6_eqrel_1(X1,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t28_eqrel_1)).

fof(cc3_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v3_relat_2(X1)
        & v8_relat_2(X1) )
     => ( v1_relat_1(X1)
        & v1_relat_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',cc3_partfun1)).

fof(dt_k7_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_subset_1(k7_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k7_eqrel_1)).

fof(redefinition_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k8_eqrel_1(X1,X2) = k7_eqrel_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k8_eqrel_1)).

fof(dt_k8_eqrel_1,axiom,(
    ! [X1,X2] :
      ( ( v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => m1_eqrel_1(k8_eqrel_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k8_eqrel_1)).

fof(dt_m2_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X2) )
     => ! [X3] :
          ( m2_filter_1(X3,X1,X2)
         => ( v1_funct_1(X3)
            & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_m2_filter_1)).

fof(redefinition_m2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(X1)) )
     => ! [X3] :
          ( m2_subset_1(X3,X1,X2)
        <=> m1_subset_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_m2_subset_1)).

fof(dt_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k9_eqrel_1)).

fof(redefinition_k4_binop_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X1) )
     => k4_binop_1(X1,X2,X3,X4) = k1_binop_1(X2,X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k4_binop_1)).

fof(redefinition_k9_eqrel_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v3_relat_2(X2)
        & v8_relat_2(X2)
        & v1_partfun1(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        & m1_subset_1(X3,X1) )
     => k9_eqrel_1(X1,X2,X3) = k11_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k9_eqrel_1)).

fof(redefinition_k6_eqrel_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_eqrel_1(X1,X2,X3,X4) = k11_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k6_eqrel_1)).

fof(c_0_21,plain,(
    ! [X52,X53] :
      ( ~ m1_eqrel_1(X53,X52)
      | m1_subset_1(X53,k1_zfmisc_1(k1_zfmisc_1(X52))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_eqrel_1])])).

fof(c_0_22,plain,(
    ! [X60] : m1_eqrel_1(esk10_1(X60),X60) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_eqrel_1])])).

fof(c_0_23,plain,(
    ! [X99,X100,X101] :
      ( ~ r2_hidden(X99,X100)
      | ~ m1_subset_1(X100,k1_zfmisc_1(X101))
      | ~ v1_xboole_0(X101) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_eqrel_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( m1_eqrel_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk10_1(X1),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,plain,(
    ! [X92,X93] :
      ( ~ m1_subset_1(X92,X93)
      | v1_xboole_0(X93)
      | r2_hidden(X92,X93) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,negated_conjecture,(
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
                    ( m1_subset_1(X4,X1)
                   => ! [X5] :
                        ( m2_filter_1(X5,X1,X2)
                       => k1_binop_1(k3_filter_1(X1,X2,X5),k6_eqrel_1(X1,X1,X2,X3),k6_eqrel_1(X1,X1,X2,X4)) = k6_eqrel_1(X1,X1,X2,k4_binop_1(X1,X5,X3,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_filter_1])).

fof(c_0_30,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_eqrel_1(X17,X16)
      | ~ v1_xboole_0(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_eqrel_1])])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,esk10_1(X2))
    | ~ v1_xboole_0(k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X62] : m1_subset_1(esk11_1(X62),X62) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_34,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | v1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_partfun1(esk2_0,esk1_0)
    & v3_relat_2(esk2_0)
    & v8_relat_2(esk2_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & m1_subset_1(esk3_0,esk1_0)
    & m1_subset_1(esk4_0,esk1_0)
    & m2_filter_1(esk5_0,esk1_0,esk2_0)
    & k1_binop_1(k3_filter_1(esk1_0,esk2_0,esk5_0),k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk4_0)) != k6_eqrel_1(esk1_0,esk1_0,esk2_0,k4_binop_1(esk1_0,esk5_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

fof(c_0_36,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( X25 != k3_filter_1(X22,X23,X24)
        | ~ r2_hidden(X26,k8_eqrel_1(X22,X23))
        | ~ r2_hidden(X27,k8_eqrel_1(X22,X23))
        | ~ r2_hidden(X28,X26)
        | ~ r2_hidden(X29,X27)
        | k1_binop_1(X25,X26,X27) = k6_eqrel_1(X22,X22,X23,k1_binop_1(X24,X28,X29))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))))
        | ~ m2_filter_1(X24,X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X22,X22),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
        | ~ v1_partfun1(X23,X22)
        | ~ v3_relat_2(X23)
        | ~ v8_relat_2(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
        | v1_xboole_0(X22) )
      & ( r2_hidden(esk6_4(X22,X23,X24,X25),k8_eqrel_1(X22,X23))
        | X25 = k3_filter_1(X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))))
        | ~ m2_filter_1(X24,X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X22,X22),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
        | ~ v1_partfun1(X23,X22)
        | ~ v3_relat_2(X23)
        | ~ v8_relat_2(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
        | v1_xboole_0(X22) )
      & ( r2_hidden(esk7_4(X22,X23,X24,X25),k8_eqrel_1(X22,X23))
        | X25 = k3_filter_1(X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))))
        | ~ m2_filter_1(X24,X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X22,X22),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
        | ~ v1_partfun1(X23,X22)
        | ~ v3_relat_2(X23)
        | ~ v8_relat_2(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
        | v1_xboole_0(X22) )
      & ( r2_hidden(esk8_4(X22,X23,X24,X25),esk6_4(X22,X23,X24,X25))
        | X25 = k3_filter_1(X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))))
        | ~ m2_filter_1(X24,X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X22,X22),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
        | ~ v1_partfun1(X23,X22)
        | ~ v3_relat_2(X23)
        | ~ v8_relat_2(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
        | v1_xboole_0(X22) )
      & ( r2_hidden(esk9_4(X22,X23,X24,X25),esk7_4(X22,X23,X24,X25))
        | X25 = k3_filter_1(X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))))
        | ~ m2_filter_1(X24,X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X22,X22),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
        | ~ v1_partfun1(X23,X22)
        | ~ v3_relat_2(X23)
        | ~ v8_relat_2(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
        | v1_xboole_0(X22) )
      & ( k1_binop_1(X25,esk6_4(X22,X23,X24,X25),esk7_4(X22,X23,X24,X25)) != k6_eqrel_1(X22,X22,X23,k1_binop_1(X24,esk8_4(X22,X23,X24,X25),esk9_4(X22,X23,X24,X25)))
        | X25 = k3_filter_1(X22,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X22,X23),k8_eqrel_1(X22,X23)),k8_eqrel_1(X22,X23))))
        | ~ m2_filter_1(X24,X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,k2_zfmisc_1(X22,X22),X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X22,X22),X22)))
        | ~ v1_partfun1(X23,X22)
        | ~ v3_relat_2(X23)
        | ~ v8_relat_2(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X22,X22)))
        | v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_filter_1])])])])])])).

fof(c_0_37,plain,(
    ! [X34,X35,X36] :
      ( ( v1_funct_1(k3_filter_1(X34,X35,X36))
        | v1_xboole_0(X34)
        | ~ v1_partfun1(X35,X34)
        | ~ v3_relat_2(X35)
        | ~ v8_relat_2(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X34)))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,k2_zfmisc_1(X34,X34),X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X34,X34),X34))) )
      & ( v1_funct_2(k3_filter_1(X34,X35,X36),k2_zfmisc_1(k8_eqrel_1(X34,X35),k8_eqrel_1(X34,X35)),k8_eqrel_1(X34,X35))
        | v1_xboole_0(X34)
        | ~ v1_partfun1(X35,X34)
        | ~ v3_relat_2(X35)
        | ~ v8_relat_2(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X34)))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,k2_zfmisc_1(X34,X34),X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X34,X34),X34))) )
      & ( m1_subset_1(k3_filter_1(X34,X35,X36),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X34,X35),k8_eqrel_1(X34,X35)),k8_eqrel_1(X34,X35))))
        | v1_xboole_0(X34)
        | ~ v1_partfun1(X35,X34)
        | ~ v3_relat_2(X35)
        | ~ v8_relat_2(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X34)))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,k2_zfmisc_1(X34,X34),X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X34,X34),X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_filter_1])])])])).

fof(c_0_38,plain,(
    ! [X89,X90,X91] :
      ( ~ v1_relat_2(X90)
      | ~ v3_relat_2(X90)
      | ~ v1_partfun1(X90,X89)
      | ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X89,X89)))
      | ~ r2_hidden(X91,X89)
      | r2_hidden(X91,k6_eqrel_1(X89,X89,X90,X91)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_eqrel_1])])])).

fof(c_0_39,plain,(
    ! [X21] :
      ( ( v1_relat_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v3_relat_2(X21)
        | ~ v8_relat_2(X21) )
      & ( v1_relat_2(X21)
        | ~ v1_relat_1(X21)
        | ~ v3_relat_2(X21)
        | ~ v8_relat_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_partfun1])])])).

fof(c_0_40,plain,(
    ! [X45,X46] :
      ( ~ v3_relat_2(X46)
      | ~ v8_relat_2(X46)
      | ~ v1_partfun1(X46,X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X45)))
      | m1_subset_1(k7_eqrel_1(X45,X46),k1_zfmisc_1(k1_zfmisc_1(X45))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_eqrel_1])])).

fof(c_0_41,plain,(
    ! [X79,X80] :
      ( ~ v3_relat_2(X80)
      | ~ v8_relat_2(X80)
      | ~ v1_partfun1(X80,X79)
      | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X79,X79)))
      | k8_eqrel_1(X79,X80) = k7_eqrel_1(X79,X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_eqrel_1])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | ~ m1_eqrel_1(X2,X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( v1_xboole_0(esk10_1(X1))
    | ~ m1_subset_1(X2,esk10_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk11_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X47,X48] :
      ( ~ v3_relat_2(X48)
      | ~ v8_relat_2(X48)
      | ~ v1_partfun1(X48,X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X47)))
      | m1_eqrel_1(k8_eqrel_1(X47,X48),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_eqrel_1])])).

fof(c_0_46,plain,(
    ! [X54,X55,X56] :
      ( ( v1_funct_1(X56)
        | ~ m2_filter_1(X56,X54,X55)
        | v1_xboole_0(X54)
        | ~ v1_relat_1(X55) )
      & ( v1_funct_2(X56,k2_zfmisc_1(X54,X54),X54)
        | ~ m2_filter_1(X56,X54,X55)
        | v1_xboole_0(X54)
        | ~ v1_relat_1(X55) )
      & ( m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X54,X54),X54)))
        | ~ m2_filter_1(X56,X54,X55)
        | v1_xboole_0(X54)
        | ~ v1_relat_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_filter_1])])])])])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k1_binop_1(X1,X5,X6) = k6_eqrel_1(X2,X2,X3,k1_binop_1(X4,X7,X8))
    | v1_xboole_0(X2)
    | X1 != k3_filter_1(X2,X3,X4)
    | ~ r2_hidden(X5,k8_eqrel_1(X2,X3))
    | ~ r2_hidden(X6,k8_eqrel_1(X2,X3))
    | ~ r2_hidden(X7,X5)
    | ~ r2_hidden(X8,X6)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_zfmisc_1(k8_eqrel_1(X2,X3),k8_eqrel_1(X2,X3)),k8_eqrel_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X2,X3),k8_eqrel_1(X2,X3)),k8_eqrel_1(X2,X3))))
    | ~ m2_filter_1(X4,X2,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ v1_partfun1(X3,X2)
    | ~ v3_relat_2(X3)
    | ~ v8_relat_2(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( m1_subset_1(k3_filter_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( v1_funct_1(k3_filter_1(X1,X2,X3))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( v1_funct_2(k3_filter_1(X1,X2,X3),k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( r2_hidden(X3,k6_eqrel_1(X2,X2,X1,X3))
    | ~ v1_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( v1_relat_2(X1)
    | ~ v1_relat_1(X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_55,plain,(
    ! [X84,X85,X86] :
      ( ( ~ m2_subset_1(X86,X84,X85)
        | m1_subset_1(X86,X85)
        | v1_xboole_0(X84)
        | v1_xboole_0(X85)
        | ~ m1_subset_1(X85,k1_zfmisc_1(X84)) )
      & ( ~ m1_subset_1(X86,X85)
        | m2_subset_1(X86,X84,X85)
        | v1_xboole_0(X84)
        | v1_xboole_0(X85)
        | ~ m1_subset_1(X85,k1_zfmisc_1(X84)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_m2_subset_1])])])])])).

fof(c_0_56,plain,(
    ! [X49,X50,X51] :
      ( v1_xboole_0(X49)
      | ~ v3_relat_2(X50)
      | ~ v8_relat_2(X50)
      | ~ v1_partfun1(X50,X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X49,X49)))
      | ~ m1_subset_1(X51,X49)
      | m2_subset_1(k9_eqrel_1(X49,X50,X51),k1_zfmisc_1(X49),k8_eqrel_1(X49,X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_eqrel_1])])])).

cnf(c_0_57,plain,
    ( m1_subset_1(k7_eqrel_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( k8_eqrel_1(X2,X1) = k7_eqrel_1(X2,X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk10_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_60,plain,
    ( v1_xboole_0(esk10_1(X1))
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_61,plain,
    ( m1_eqrel_1(k8_eqrel_1(X2,X1),X2)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_62,plain,(
    ! [X71,X72,X73,X74] :
      ( ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,k2_zfmisc_1(X71,X71),X71)
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X71,X71),X71)))
      | ~ m1_subset_1(X73,X71)
      | ~ m1_subset_1(X74,X71)
      | k4_binop_1(X71,X72,X73,X74) = k1_binop_1(X72,X73,X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_binop_1])])).

cnf(c_0_63,plain,
    ( v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,negated_conjecture,
    ( m2_filter_1(esk5_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_67,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | v1_xboole_0(X2)
    | ~ m2_filter_1(X1,X2,X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_69,plain,
    ( k1_binop_1(k3_filter_1(X1,X2,X3),X4,X5) = k6_eqrel_1(X1,X1,X2,k1_binop_1(X3,X6,X7))
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X5,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X4,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X7,X5)
    | ~ r2_hidden(X6,X4)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k6_eqrel_1(X2,X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v8_relat_2(X3)
    | ~ v3_relat_2(X3)
    | ~ v1_partfun1(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_47])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ m2_subset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_72,plain,
    ( v1_xboole_0(X1)
    | m2_subset_1(k9_eqrel_1(X1,X2,X3),k1_zfmisc_1(X1),k8_eqrel_1(X1,X2))
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,plain,
    ( m1_subset_1(k8_eqrel_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_xboole_0(k8_eqrel_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_61])).

fof(c_0_76,plain,(
    ! [X81,X82,X83] :
      ( v1_xboole_0(X81)
      | ~ v3_relat_2(X82)
      | ~ v8_relat_2(X82)
      | ~ v1_partfun1(X82,X81)
      | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X81,X81)))
      | ~ m1_subset_1(X83,X81)
      | k9_eqrel_1(X81,X82,X83) = k11_relat_1(X82,X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k9_eqrel_1])])])).

cnf(c_0_77,negated_conjecture,
    ( k1_binop_1(k3_filter_1(esk1_0,esk2_0,esk5_0),k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk4_0)) != k6_eqrel_1(esk1_0,esk1_0,esk2_0,k4_binop_1(esk1_0,esk5_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_78,plain,
    ( k4_binop_1(X2,X1,X3,X4) = k1_binop_1(X1,X3,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k2_zfmisc_1(X2,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_zfmisc_1(esk1_0,esk1_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_64]),c_0_65])]),c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_64]),c_0_65])]),c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_84,plain,
    ( k1_binop_1(k3_filter_1(X1,X2,X3),X4,k6_eqrel_1(X5,X5,X6,X7)) = k6_eqrel_1(X1,X1,X2,k1_binop_1(X3,X8,X7))
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(k6_eqrel_1(X5,X5,X6,X7),k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X4,k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X8,X4)
    | ~ r2_hidden(X7,X5)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
    | ~ v8_relat_2(X2)
    | ~ v8_relat_2(X6)
    | ~ v3_relat_2(X2)
    | ~ v3_relat_2(X6)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_partfun1(X6,X5) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_85,plain,
    ( m1_subset_1(k9_eqrel_1(X1,X2,X3),k8_eqrel_1(X1,X2))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ v8_relat_2(X2)
    | ~ v3_relat_2(X2)
    | ~ v1_partfun1(X2,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_75])).

cnf(c_0_86,plain,
    ( v1_xboole_0(X1)
    | k9_eqrel_1(X1,X2,X3) = k11_relat_1(X2,X3)
    | ~ v3_relat_2(X2)
    | ~ v8_relat_2(X2)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( k1_binop_1(k3_filter_1(esk1_0,esk2_0,esk5_0),k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk4_0)) != k6_eqrel_1(esk1_0,esk1_0,esk2_0,k1_binop_1(esk5_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80]),c_0_81]),c_0_82]),c_0_83])])).

cnf(c_0_88,plain,
    ( k1_binop_1(k3_filter_1(X1,X2,X3),k6_eqrel_1(X4,X4,X5,X6),k6_eqrel_1(X7,X7,X8,X9)) = k6_eqrel_1(X1,X1,X2,k1_binop_1(X3,X6,X9))
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(k6_eqrel_1(X7,X7,X8,X9),k8_eqrel_1(X1,X2))
    | ~ r2_hidden(k6_eqrel_1(X4,X4,X5,X6),k8_eqrel_1(X1,X2))
    | ~ r2_hidden(X9,X7)
    | ~ r2_hidden(X6,X4)
    | ~ m2_filter_1(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))
    | ~ v8_relat_2(X2)
    | ~ v8_relat_2(X8)
    | ~ v8_relat_2(X5)
    | ~ v3_relat_2(X2)
    | ~ v3_relat_2(X8)
    | ~ v3_relat_2(X5)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_partfun1(X8,X7)
    | ~ v1_partfun1(X5,X4) ),
    inference(spm,[status(thm)],[c_0_84,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( v8_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_90,negated_conjecture,
    ( v3_relat_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( v1_partfun1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_92,plain,
    ( m1_subset_1(k11_relat_1(X1,X2),k8_eqrel_1(X3,X1))
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))
    | ~ m1_subset_1(X2,X3)
    | ~ v8_relat_2(X1)
    | ~ v3_relat_2(X1)
    | ~ v1_partfun1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

fof(c_0_93,plain,(
    ! [X75,X76,X77,X78] :
      ( ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
      | k6_eqrel_1(X75,X76,X77,X78) = k11_relat_1(X77,X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_eqrel_1])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk4_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ r2_hidden(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk4_0,esk1_0)
    | ~ r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_79]),c_0_80]),c_0_64]),c_0_81]),c_0_48]),c_0_89]),c_0_90]),c_0_91])]),c_0_66])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_xboole_0(k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_91]),c_0_48]),c_0_89]),c_0_90])]),c_0_66])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k11_relat_1(esk2_0,X1),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_91]),c_0_48]),c_0_89]),c_0_90])]),c_0_66])).

cnf(c_0_97,plain,
    ( k6_eqrel_1(X2,X3,X1,X4) = k11_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_hidden(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk4_0,esk1_0)
    | ~ r2_hidden(esk3_0,esk1_0)
    | ~ m1_subset_1(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk4_0),k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_32]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k6_eqrel_1(X1,X2,esk2_0,X3),k8_eqrel_1(esk1_0,esk2_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,esk1_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk4_0,esk1_0)
    | ~ r2_hidden(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_48]),c_0_82])])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_32]),c_0_82])]),c_0_66])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk1_0)
    | ~ m1_subset_1(k6_eqrel_1(esk1_0,esk1_0,esk2_0,esk3_0),k8_eqrel_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_32]),c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_99]),c_0_48]),c_0_83])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_32]),c_0_83])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
