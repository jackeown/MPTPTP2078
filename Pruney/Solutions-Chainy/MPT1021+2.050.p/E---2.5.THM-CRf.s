%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:13 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 442 expanded)
%              Number of clauses        :   46 ( 148 expanded)
%              Number of leaves         :   16 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  260 (2015 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

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

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t62_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk2_0,esk2_0)
    & v3_funct_2(esk3_0,esk2_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))
      | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_18,plain,(
    ! [X37] : k6_partfun1(X37) = k6_relat_1(X37) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_19,plain,(
    ! [X35,X36] :
      ( ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,X35,X35)
      | ~ v3_funct_2(X36,X35,X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35)))
      | k2_funct_2(X35,X36) = k2_funct_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_20,plain,(
    ! [X26,X27] :
      ( ( v1_funct_1(k2_funct_2(X26,X27))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X26,X26)
        | ~ v3_funct_2(X27,X26,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) )
      & ( v1_funct_2(k2_funct_2(X26,X27),X26,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X26,X26)
        | ~ v3_funct_2(X27,X26,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) )
      & ( v3_funct_2(k2_funct_2(X26,X27),X26,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X26,X26)
        | ~ v3_funct_2(X27,X26,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) )
      & ( m1_subset_1(k2_funct_2(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X26,X26)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X26,X26)
        | ~ v3_funct_2(X27,X26,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v3_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k2_funct_2(esk2_0,esk3_0) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

fof(c_0_31,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ~ v1_funct_1(X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ v1_funct_1(X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_partfun1(X29,X30,X31,X32,X33,X34) = k5_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

fof(c_0_33,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_34,plain,(
    ! [X38,X39] :
      ( ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,X38,X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X38)))
      | k1_relset_1(X38,X38,X39) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_36,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X23,X24,X25] :
      ( ( v1_funct_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v3_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v2_funct_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v3_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v2_funct_2(X25,X24)
        | ~ v1_funct_1(X25)
        | ~ v3_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_41,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27]),c_0_37]),c_0_24])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_44,plain,(
    ! [X10] :
      ( ( k5_relat_1(X10,k2_funct_1(X10)) = k6_relat_1(k1_relat_1(X10))
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k5_relat_1(k2_funct_1(X10),X10) = k6_relat_1(k2_relat_1(X10))
        | ~ v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_45,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v2_funct_1(X12)
      | k2_funct_1(k2_funct_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_49,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_50,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v2_funct_1(X11)
      | v2_funct_1(k2_funct_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).

cnf(c_0_51,plain,
    ( v1_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_37]),c_0_27]),c_0_24])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_25]),c_0_26]),c_0_27]),c_0_24])])).

cnf(c_0_54,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25]),c_0_27])])).

cnf(c_0_56,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_24]),c_0_26]),c_0_27])])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_58,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_30]),c_0_25]),c_0_26]),c_0_27]),c_0_24])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_64,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_27]),c_0_57])])).

cnf(c_0_65,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_58]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_53]),c_0_62]),c_0_37])])).

fof(c_0_67,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | r2_relset_1(X19,X20,X21,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

fof(c_0_68,plain,(
    ! [X7] :
      ( m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))
      & ~ v1_subset_1(esk1_1(X7),X7) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_69,plain,(
    ! [X28] :
      ( v1_partfun1(k6_partfun1(X28),X28)
      & m1_subset_1(k6_partfun1(X28),k1_zfmisc_1(k2_zfmisc_1(X28,X28))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_56]),c_0_27]),c_0_57])])).

cnf(c_0_72,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_76,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:20:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 0.12/0.37  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.37  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.12/0.38  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.12/0.38  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.12/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.38  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.12/0.38  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.12/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.38  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.12/0.38  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 0.12/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.12/0.38  fof(t62_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 0.12/0.38  fof(reflexivity_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_relset_1(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 0.12/0.38  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.12/0.38  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.12/0.38  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.12/0.38  fof(c_0_17, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&v3_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.12/0.38  fof(c_0_18, plain, ![X37]:k6_partfun1(X37)=k6_relat_1(X37), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.38  fof(c_0_19, plain, ![X35, X36]:(~v1_funct_1(X36)|~v1_funct_2(X36,X35,X35)|~v3_funct_2(X36,X35,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35)))|k2_funct_2(X35,X36)=k2_funct_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.12/0.38  fof(c_0_20, plain, ![X26, X27]:((((v1_funct_1(k2_funct_2(X26,X27))|(~v1_funct_1(X27)|~v1_funct_2(X27,X26,X26)|~v3_funct_2(X27,X26,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26)))))&(v1_funct_2(k2_funct_2(X26,X27),X26,X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,X26,X26)|~v3_funct_2(X27,X26,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))))))&(v3_funct_2(k2_funct_2(X26,X27),X26,X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,X26,X26)|~v3_funct_2(X27,X26,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26))))))&(m1_subset_1(k2_funct_2(X26,X27),k1_zfmisc_1(k2_zfmisc_1(X26,X26)))|(~v1_funct_1(X27)|~v1_funct_2(X27,X26,X26)|~v3_funct_2(X27,X26,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_22, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_23, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (v3_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_28, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (k2_funct_2(esk2_0,esk3_0)=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])])).
% 0.12/0.38  fof(c_0_31, plain, ![X29, X30, X31, X32, X33, X34]:(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_partfun1(X29,X30,X31,X32,X33,X34)=k5_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(k2_funct_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_25]), c_0_26]), c_0_27])])).
% 0.12/0.38  fof(c_0_33, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.38  fof(c_0_34, plain, ![X38, X39]:(~v1_funct_1(X39)|~v1_funct_2(X39,X38,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X38,X38)))|k1_relset_1(X38,X38,X39)=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.12/0.38  cnf(c_0_36, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(rw,[status(thm)],[c_0_32, c_0_30])).
% 0.12/0.38  cnf(c_0_38, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.38  cnf(c_0_39, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.38  fof(c_0_40, plain, ![X23, X24, X25]:(((v1_funct_1(X25)|(~v1_funct_1(X25)|~v3_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v2_funct_1(X25)|(~v1_funct_1(X25)|~v3_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(v2_funct_2(X25,X24)|(~v1_funct_1(X25)|~v3_funct_2(X25,X23,X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.12/0.38  fof(c_0_41, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_27]), c_0_37]), c_0_24])])).
% 0.12/0.38  cnf(c_0_43, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  fof(c_0_44, plain, ![X10]:((k5_relat_1(X10,k2_funct_1(X10))=k6_relat_1(k1_relat_1(X10))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(k5_relat_1(k2_funct_1(X10),X10)=k6_relat_1(k2_relat_1(X10))|~v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.12/0.38  cnf(c_0_45, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.38  cnf(c_0_46, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_47, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.38  fof(c_0_48, plain, ![X12]:(~v1_relat_1(X12)|~v1_funct_1(X12)|(~v2_funct_1(X12)|k2_funct_1(k2_funct_1(X12))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.12/0.38  fof(c_0_49, plain, ![X9]:((v1_relat_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.12/0.38  fof(c_0_50, plain, ![X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v2_funct_1(X11)|v2_funct_1(k2_funct_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).
% 0.12/0.38  cnf(c_0_51, plain, (v1_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_37]), c_0_27]), c_0_24])])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_25]), c_0_26]), c_0_27]), c_0_24])])).
% 0.12/0.38  cnf(c_0_54, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_25]), c_0_27])])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_24]), c_0_26]), c_0_27])])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_24])).
% 0.12/0.38  cnf(c_0_58, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_59, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_60, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_61, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_30]), c_0_25]), c_0_26]), c_0_27]), c_0_24])])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_1(esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_27]), c_0_57])])).
% 0.12/0.38  cnf(c_0_65, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_53]), c_0_62]), c_0_37])])).
% 0.12/0.38  fof(c_0_67, plain, ![X19, X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|r2_relset_1(X19,X20,X21,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).
% 0.12/0.38  fof(c_0_68, plain, ![X7]:(m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))&~v1_subset_1(esk1_1(X7),X7)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.12/0.38  fof(c_0_69, plain, ![X28]:(v1_partfun1(k6_partfun1(X28),X28)&m1_subset_1(k6_partfun1(X28),k1_zfmisc_1(k2_zfmisc_1(X28,X28)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_1(esk3_0),esk3_0),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_56]), c_0_27]), c_0_57])])).
% 0.12/0.38  cnf(c_0_72, plain, (r2_relset_1(X2,X3,X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.12/0.38  cnf(c_0_73, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.12/0.38  cnf(c_0_74, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.12/0.38  cnf(c_0_76, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.12/0.38  cnf(c_0_77, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_74, c_0_22])).
% 0.12/0.38  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 79
% 0.12/0.38  # Proof object clause steps            : 46
% 0.12/0.38  # Proof object formula steps           : 33
% 0.12/0.38  # Proof object conjectures             : 27
% 0.12/0.38  # Proof object clause conjectures      : 24
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 23
% 0.12/0.38  # Proof object initial formulas used   : 16
% 0.12/0.38  # Proof object generating inferences   : 16
% 0.12/0.38  # Proof object simplifying inferences  : 59
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 16
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 29
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 27
% 0.12/0.38  # Processed clauses                    : 140
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 5
% 0.12/0.38  # ...remaining for further processing  : 134
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 14
% 0.12/0.38  # Generated clauses                    : 243
% 0.12/0.38  # ...of the previous two non-trivial   : 170
% 0.12/0.38  # Contextual simplify-reflections      : 3
% 0.12/0.38  # Paramodulations                      : 243
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
% 0.12/0.38  # Current number of processed clauses  : 92
% 0.12/0.38  #    Positive orientable unit clauses  : 56
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 34
% 0.12/0.38  # Current number of unprocessed clauses: 80
% 0.12/0.38  # ...number of literals in the above   : 377
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 43
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 438
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 99
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.12/0.38  # Unit Clause-clause subsumption calls : 12
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 32
% 0.12/0.38  # BW rewrite match successes           : 7
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 7741
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.035 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.041 s
% 0.12/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
