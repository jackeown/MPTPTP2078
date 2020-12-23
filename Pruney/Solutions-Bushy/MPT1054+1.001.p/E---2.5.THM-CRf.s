%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 109 expanded)
%              Number of clauses        :   30 (  46 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :  165 ( 261 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc4_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( ( v1_relat_2(X2)
          & v1_funct_1(X2)
          & v1_partfun1(X2,X1)
          & v1_funct_2(X2,X1,X1) )
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(fc3_partfun1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v3_relat_2(k6_relat_1(X1))
      & v4_relat_2(k6_relat_1(X1))
      & v8_relat_2(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_partfun1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc3_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v3_relat_2(X1)
        & v8_relat_2(X1) )
     => ( v1_relat_1(X1)
        & v1_relat_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_partfun1)).

fof(t171_funct_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(t162_funct_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k9_relat_1(k6_relat_1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(t92_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X1)
        & v3_funct_2(X3,X1,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r1_tarski(X2,X1)
       => ( k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2)) = X2
          & k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( v1_funct_1(X10)
        | ~ v1_relat_2(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_partfun1(X10,X9)
        | ~ v1_funct_2(X10,X9,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( v1_funct_2(X10,X9,X9)
        | ~ v1_relat_2(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_partfun1(X10,X9)
        | ~ v1_funct_2(X10,X9,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( v3_funct_2(X10,X9,X9)
        | ~ v1_relat_2(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_partfun1(X10,X9)
        | ~ v1_funct_2(X10,X9,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_funct_2])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( ( v1_funct_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) )
      & ( v1_funct_2(X7,X5,X6)
        | ~ v1_funct_1(X7)
        | ~ v1_partfun1(X7,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_14,plain,(
    ! [X12] :
      ( v1_relat_1(k6_relat_1(X12))
      & v1_funct_1(k6_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_15,plain,(
    ! [X14] : k6_partfun1(X14) = k6_relat_1(X14) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_16,plain,
    ( v3_funct_2(X1,X2,X2)
    | ~ v1_relat_2(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X11] :
      ( v1_partfun1(k6_partfun1(X11),X11)
      & m1_subset_1(k6_partfun1(X11),k1_zfmisc_1(k2_zfmisc_1(X11,X11))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_19,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X13] :
      ( v1_relat_1(k6_relat_1(X13))
      & v3_relat_2(k6_relat_1(X13))
      & v4_relat_2(k6_relat_1(X13))
      & v8_relat_2(k6_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[fc3_partfun1])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k7_relset_1(X15,X16,X17,X18) = k9_relat_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_23,plain,
    ( v3_funct_2(X1,X2,X2)
    | ~ v1_relat_2(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_27,plain,(
    ! [X8] :
      ( ( v1_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v3_relat_2(X8)
        | ~ v8_relat_2(X8) )
      & ( v1_relat_2(X8)
        | ~ v1_relat_1(X8)
        | ~ v3_relat_2(X8)
        | ~ v8_relat_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_partfun1])])])).

cnf(c_0_28,plain,
    ( v8_relat_2(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v3_relat_2(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t171_funct_2])).

fof(c_0_32,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k9_relat_1(k6_relat_1(X19),X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_funct_1])])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] :
      ( ( k7_relset_1(X23,X23,X25,k8_relset_1(X23,X23,X25,X24)) = X24
        | ~ r1_tarski(X24,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X23)
        | ~ v3_funct_2(X25,X23,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) )
      & ( k8_relset_1(X23,X23,X25,k7_relset_1(X23,X23,X25,X24)) = X24
        | ~ r1_tarski(X24,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X23)
        | ~ v3_funct_2(X25,X23,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_funct_2])])])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v3_funct_2(k6_partfun1(X1),X1,X1)
    | ~ v1_relat_2(k6_partfun1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_36,plain,
    ( v1_relat_2(X1)
    | ~ v1_relat_1(X1)
    | ~ v3_relat_2(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v8_relat_2(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_38,plain,
    ( v3_relat_2(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_39,plain,
    ( v1_relat_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_20])).

fof(c_0_40,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_42,plain,
    ( k9_relat_1(k6_relat_1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k8_relset_1(X1,X1,X2,k7_relset_1(X1,X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v1_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_45,plain,
    ( k7_relset_1(X1,X1,k6_partfun1(X1),X2) = k9_relat_1(k6_partfun1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_24])).

cnf(c_0_46,plain,
    ( v3_funct_2(k6_partfun1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k9_relat_1(k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_50,plain,
    ( k8_relset_1(X1,X1,k6_partfun1(X1),k9_relat_1(k6_partfun1(X1),X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26]),c_0_24])]),c_0_45]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k9_relat_1(k6_partfun1(esk1_0),esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k8_relset_1(esk1_0,esk1_0,k6_partfun1(esk1_0),esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),
    [proof]).

%------------------------------------------------------------------------------
