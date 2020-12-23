%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:12 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 269 expanded)
%              Number of clauses        :   42 (  92 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 (1196 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
        & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk2_0,esk2_0)
    & v3_funct_2(esk3_0,esk2_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))
      | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X39] : k6_partfun1(X39) = k6_relat_1(X39) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_18,plain,(
    ! [X29,X30] :
      ( ( v1_funct_1(k2_funct_2(X29,X30))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X29,X29)
        | ~ v3_funct_2(X30,X29,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29))) )
      & ( v1_funct_2(k2_funct_2(X29,X30),X29,X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X29,X29)
        | ~ v3_funct_2(X30,X29,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29))) )
      & ( v3_funct_2(k2_funct_2(X29,X30),X29,X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X29,X29)
        | ~ v3_funct_2(X30,X29,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29))) )
      & ( m1_subset_1(k2_funct_2(X29,X30),k1_zfmisc_1(k2_zfmisc_1(X29,X29)))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X29,X29)
        | ~ v3_funct_2(X30,X29,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ( v1_funct_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v3_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v2_funct_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v3_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v2_funct_2(X26,X25)
        | ~ v1_funct_1(X26)
        | ~ v3_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ( v4_relat_1(X15,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v5_relat_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ v1_funct_1(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_partfun1(X31,X32,X33,X34,X35,X36) = k5_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_25,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v3_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X37,X38] :
      ( ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,X37,X37)
      | ~ v3_funct_2(X38,X37,X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X37)))
      | k2_funct_2(X37,X38) = k2_funct_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_31,plain,(
    ! [X27,X28] :
      ( ( ~ v2_funct_2(X28,X27)
        | k2_relat_1(X28) = X27
        | ~ v1_relat_1(X28)
        | ~ v5_relat_1(X28,X27) )
      & ( k2_relat_1(X28) != X27
        | v2_funct_2(X28,X27)
        | ~ v1_relat_1(X28)
        | ~ v5_relat_1(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_32,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_35,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_36,plain,(
    ! [X40,X41] :
      ( ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,X40,X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X40)))
      | k1_relset_1(X40,X40,X41) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_38,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])])).

fof(c_0_40,plain,(
    ! [X9] :
      ( ( k5_relat_1(X9,k2_funct_1(X9)) = k6_relat_1(k1_relat_1(X9))
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( k5_relat_1(k2_funct_1(X9),X9) = k6_relat_1(k2_relat_1(X9))
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_41,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v2_funct_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_28]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_46,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_29]),c_0_39]),c_0_26])])).

cnf(c_0_50,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_funct_2(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_52,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_53,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_28]),c_0_29])])).

cnf(c_0_54,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_39]),c_0_29]),c_0_26])])).

cnf(c_0_57,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_29]),c_0_45])])).

cnf(c_0_58,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) = k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_53]),c_0_29]),c_0_45])])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_26]),c_0_27]),c_0_29])])).

fof(c_0_60,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | r2_relset_1(X19,X20,X21,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

fof(c_0_61,plain,(
    ! [X7] : m1_subset_1(esk1_1(X7),X7) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_66,plain,(
    ! [X23] : m1_subset_1(k6_relat_1(X23),k1_zfmisc_1(k2_zfmisc_1(X23,X23))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_68,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_27]),c_0_28]),c_0_29]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.30  % Computer   : n013.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % WCLimit    : 600
% 0.12/0.30  % DateTime   : Tue Dec  1 13:00:09 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.31  # No SInE strategy applied
% 0.12/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.028 s
% 0.16/0.34  # Presaturation interreduction done
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 0.16/0.34  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.16/0.34  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.16/0.34  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.16/0.34  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.16/0.34  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.16/0.34  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.16/0.34  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.16/0.34  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.16/0.34  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.16/0.34  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.16/0.34  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.16/0.34  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.16/0.34  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.16/0.34  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.16/0.34  fof(c_0_15, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.16/0.34  fof(c_0_16, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&v3_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.16/0.34  fof(c_0_17, plain, ![X39]:k6_partfun1(X39)=k6_relat_1(X39), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.16/0.34  fof(c_0_18, plain, ![X29, X30]:((((v1_funct_1(k2_funct_2(X29,X30))|(~v1_funct_1(X30)|~v1_funct_2(X30,X29,X29)|~v3_funct_2(X30,X29,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29)))))&(v1_funct_2(k2_funct_2(X29,X30),X29,X29)|(~v1_funct_1(X30)|~v1_funct_2(X30,X29,X29)|~v3_funct_2(X30,X29,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29))))))&(v3_funct_2(k2_funct_2(X29,X30),X29,X29)|(~v1_funct_1(X30)|~v1_funct_2(X30,X29,X29)|~v3_funct_2(X30,X29,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29))))))&(m1_subset_1(k2_funct_2(X29,X30),k1_zfmisc_1(k2_zfmisc_1(X29,X29)))|(~v1_funct_1(X30)|~v1_funct_2(X30,X29,X29)|~v3_funct_2(X30,X29,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X29,X29)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.16/0.34  fof(c_0_19, plain, ![X24, X25, X26]:(((v1_funct_1(X26)|(~v1_funct_1(X26)|~v3_funct_2(X26,X24,X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(v2_funct_1(X26)|(~v1_funct_1(X26)|~v3_funct_2(X26,X24,X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&(v2_funct_2(X26,X25)|(~v1_funct_1(X26)|~v3_funct_2(X26,X24,X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.16/0.34  fof(c_0_20, plain, ![X13, X14, X15]:((v4_relat_1(X15,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))&(v5_relat_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.16/0.34  fof(c_0_21, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.16/0.34  cnf(c_0_22, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.34  cnf(c_0_23, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.34  fof(c_0_24, plain, ![X31, X32, X33, X34, X35, X36]:(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_partfun1(X31,X32,X33,X34,X35,X36)=k5_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.16/0.34  cnf(c_0_25, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.34  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.34  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.34  cnf(c_0_28, negated_conjecture, (v3_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.34  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.34  fof(c_0_30, plain, ![X37, X38]:(~v1_funct_1(X38)|~v1_funct_2(X38,X37,X37)|~v3_funct_2(X38,X37,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X37)))|k2_funct_2(X37,X38)=k2_funct_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.16/0.34  fof(c_0_31, plain, ![X27, X28]:((~v2_funct_2(X28,X27)|k2_relat_1(X28)=X27|(~v1_relat_1(X28)|~v5_relat_1(X28,X27)))&(k2_relat_1(X28)!=X27|v2_funct_2(X28,X27)|(~v1_relat_1(X28)|~v5_relat_1(X28,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.16/0.34  cnf(c_0_32, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.34  cnf(c_0_33, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.16/0.34  cnf(c_0_34, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.34  fof(c_0_35, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.16/0.34  fof(c_0_36, plain, ![X40, X41]:(~v1_funct_1(X41)|~v1_funct_2(X41,X40,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X40)))|k1_relset_1(X40,X40,X41)=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.16/0.34  cnf(c_0_37, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.16/0.34  cnf(c_0_38, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.16/0.34  cnf(c_0_39, negated_conjecture, (v1_funct_1(k2_funct_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])])).
% 0.16/0.34  fof(c_0_40, plain, ![X9]:((k5_relat_1(X9,k2_funct_1(X9))=k6_relat_1(k1_relat_1(X9))|~v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(k5_relat_1(k2_funct_1(X9),X9)=k6_relat_1(k2_relat_1(X9))|~v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.16/0.34  cnf(c_0_41, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.34  cnf(c_0_42, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.34  cnf(c_0_43, negated_conjecture, (v2_funct_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_28]), c_0_29])])).
% 0.16/0.34  cnf(c_0_44, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.16/0.34  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.16/0.34  cnf(c_0_46, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.16/0.34  cnf(c_0_47, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.34  cnf(c_0_48, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.34  cnf(c_0_49, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_29]), c_0_39]), c_0_26])])).
% 0.16/0.34  cnf(c_0_50, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  cnf(c_0_51, negated_conjecture, (k2_funct_1(esk3_0)=k2_funct_2(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_27]), c_0_28]), c_0_29])])).
% 0.16/0.34  cnf(c_0_52, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])])).
% 0.16/0.34  cnf(c_0_53, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_26]), c_0_28]), c_0_29])])).
% 0.16/0.34  cnf(c_0_54, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  cnf(c_0_55, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.16/0.34  cnf(c_0_56, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_39]), c_0_29]), c_0_26])])).
% 0.16/0.34  cnf(c_0_57, negated_conjecture, (k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_29]), c_0_45])])).
% 0.16/0.34  cnf(c_0_58, negated_conjecture, (k6_relat_1(k1_relat_1(esk3_0))=k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_53]), c_0_29]), c_0_45])])).
% 0.16/0.34  cnf(c_0_59, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_26]), c_0_27]), c_0_29])])).
% 0.16/0.34  fof(c_0_60, plain, ![X19, X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|r2_relset_1(X19,X20,X21,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.16/0.34  fof(c_0_61, plain, ![X7]:m1_subset_1(esk1_1(X7),X7), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.16/0.34  cnf(c_0_62, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.16/0.34  cnf(c_0_63, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.16/0.34  cnf(c_0_64, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.16/0.34  cnf(c_0_65, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.16/0.34  fof(c_0_66, plain, ![X23]:m1_subset_1(k6_relat_1(X23),k1_zfmisc_1(k2_zfmisc_1(X23,X23))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.16/0.34  cnf(c_0_67, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.16/0.34  cnf(c_0_68, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.16/0.34  cnf(c_0_69, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.16/0.34  cnf(c_0_70, negated_conjecture, (~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.16/0.34  cnf(c_0_71, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.34  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_27]), c_0_28]), c_0_29]), c_0_26])]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 73
% 0.16/0.34  # Proof object clause steps            : 42
% 0.16/0.34  # Proof object formula steps           : 31
% 0.16/0.34  # Proof object conjectures             : 26
% 0.16/0.34  # Proof object clause conjectures      : 23
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 22
% 0.16/0.34  # Proof object initial formulas used   : 15
% 0.16/0.34  # Proof object generating inferences   : 16
% 0.16/0.34  # Proof object simplifying inferences  : 50
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 15
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 27
% 0.16/0.34  # Removed in clause preprocessing      : 2
% 0.16/0.34  # Initial clauses in saturation        : 25
% 0.16/0.34  # Processed clauses                    : 80
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 1
% 0.16/0.34  # ...remaining for further processing  : 79
% 0.16/0.34  # Other redundant clauses eliminated   : 1
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 3
% 0.16/0.34  # Backward-rewritten                   : 4
% 0.16/0.34  # Generated clauses                    : 53
% 0.16/0.34  # ...of the previous two non-trivial   : 55
% 0.16/0.34  # Contextual simplify-reflections      : 0
% 0.16/0.34  # Paramodulations                      : 52
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 1
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 46
% 0.16/0.34  #    Positive orientable unit clauses  : 22
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 1
% 0.16/0.34  #    Non-unit-clauses                  : 23
% 0.16/0.34  # Current number of unprocessed clauses: 24
% 0.16/0.34  # ...number of literals in the above   : 97
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 33
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 459
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 128
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 4
% 0.16/0.34  # Unit Clause-clause subsumption calls : 21
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 3
% 0.16/0.34  # BW rewrite match successes           : 3
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 3522
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.033 s
% 0.16/0.34  # System time              : 0.004 s
% 0.16/0.34  # Total time               : 0.037 s
% 0.16/0.34  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
