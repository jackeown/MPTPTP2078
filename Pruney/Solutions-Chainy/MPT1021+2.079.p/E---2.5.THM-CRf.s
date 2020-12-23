%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 555 expanded)
%              Number of clauses        :   57 ( 191 expanded)
%              Number of leaves         :   14 ( 143 expanded)
%              Depth                    :   17
%              Number of atoms          :  353 (2889 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t87_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & v3_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))
           => r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ( v1_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v3_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v2_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v3_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v2_funct_2(X22,X21)
        | ~ v1_funct_1(X22)
        | ~ v3_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & v3_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))
      | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] :
      ( ( v4_relat_1(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( v5_relat_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_19,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_20,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,X36,X36)
      | ~ v3_funct_2(X37,X36,X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,X36,X36)
      | ~ v3_funct_2(X38,X36,X36)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))
      | ~ r2_relset_1(X36,X36,k1_partfun1(X36,X36,X36,X36,X37,X38),k6_partfun1(X36))
      | r2_relset_1(X36,X36,X38,k2_funct_2(X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_2])])])).

fof(c_0_21,plain,(
    ! [X35] : k6_partfun1(X35) = k6_relat_1(X35) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_22,plain,(
    ! [X33,X34] :
      ( ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,X33,X33)
      | ~ v3_funct_2(X34,X33,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33)))
      | k2_funct_2(X33,X34) = k2_funct_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( ( ~ v2_funct_2(X24,X23)
        | k2_relat_1(X24) = X23
        | ~ v1_relat_1(X24)
        | ~ v5_relat_1(X24,X23) )
      & ( k2_relat_1(X24) != X23
        | v2_funct_2(X24,X23)
        | ~ v1_relat_1(X24)
        | ~ v5_relat_1(X24,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_24,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_relset_1(X2,X2,X3,k2_funct_2(X2,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X2)
    | ~ v3_funct_2(X3,X2,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X2,X2,X2,X1,X3),k6_partfun1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ~ v1_funct_1(X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ v1_funct_1(X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_partfun1(X27,X28,X29,X30,X31,X32) = k5_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_34,plain,(
    ! [X11] :
      ( ( k5_relat_1(X11,k2_funct_1(X11)) = k6_relat_1(k1_relat_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( k5_relat_1(k2_funct_1(X11),X11) = k6_relat_1(k2_relat_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_35,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_39,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_30])])).

cnf(c_0_41,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X25,X26] :
      ( ( v1_funct_1(k2_funct_2(X25,X26))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X25,X25)
        | ~ v3_funct_2(X26,X25,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) )
      & ( v1_funct_2(k2_funct_2(X25,X26),X25,X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X25,X25)
        | ~ v3_funct_2(X26,X25,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) )
      & ( v3_funct_2(k2_funct_2(X25,X26),X25,X25)
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X25,X25)
        | ~ v3_funct_2(X26,X25,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) )
      & ( m1_subset_1(k2_funct_2(X25,X26),k1_zfmisc_1(k2_zfmisc_1(X25,X25)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X25,X25)
        | ~ v3_funct_2(X26,X25,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_43,plain,
    ( r2_relset_1(X2,X2,X3,k2_funct_2(X2,X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X3,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ v1_funct_2(X3,X2,X2)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X2,X2,X2,X1,X3),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k2_funct_1(esk2_0) = k2_funct_2(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_36]),c_0_26]),c_0_27])])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_48,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_49,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_relset_1(X15,X16,X17,X18)
        | X17 = X18
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != X18
        | r2_relset_1(X15,X16,X17,X18)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_51,plain,
    ( r2_relset_1(X1,X1,X2,k2_funct_2(X1,X3))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_2(X3,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X3,X1,X1)
    | ~ r2_relset_1(X1,X1,k5_relat_1(X3,X2),k6_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_27]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_25]),c_0_36]),c_0_26]),c_0_27])])).

cnf(c_0_54,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_55,plain,(
    ! [X19] : m1_subset_1(k6_relat_1(X19),k1_zfmisc_1(k2_zfmisc_1(X19,X19))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_56,negated_conjecture,
    ( r2_relset_1(X1,X1,esk2_0,k2_funct_2(X1,k2_funct_2(esk1_0,esk2_0)))
    | ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),X1,X1)
    | ~ v1_funct_2(esk2_0,X1,X1)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),X1,X1)
    | ~ v3_funct_2(esk2_0,X1,X1)
    | ~ r2_relset_1(X1,X1,k6_relat_1(esk1_0),k6_relat_1(X1))
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_27]),c_0_53])])).

cnf(c_0_57,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_58,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)))
    | ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36]),c_0_26]),c_0_25]),c_0_58])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,plain,
    ( v3_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_32]),c_0_32])).

cnf(c_0_65,plain,
    ( v1_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)) = esk2_0
    | ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ m1_subset_1(k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25])])).

cnf(c_0_67,plain,
    ( v2_funct_2(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_62]),c_0_49]),c_0_63])).

cnf(c_0_68,plain,
    ( v1_relat_1(k2_funct_2(X1,X2))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_62]),c_0_30])])).

cnf(c_0_69,plain,
    ( v5_relat_1(k2_funct_2(X1,X2),X1)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_44]),c_0_27]),c_0_53]),c_0_25])])).

cnf(c_0_71,plain,
    ( k2_funct_2(X1,k2_funct_2(X1,X2)) = k2_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_62]),c_0_49]),c_0_63]),c_0_65])).

cnf(c_0_72,plain,
    ( v2_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_62]),c_0_49]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)) = esk2_0
    | ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_62]),c_0_53])])).

cnf(c_0_74,plain,
    ( k2_relat_1(k2_funct_2(X1,X2)) = X1
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_44]),c_0_53]),c_0_27]),c_0_25])])).

cnf(c_0_76,plain,
    ( k5_relat_1(k2_funct_2(X1,k2_funct_2(X1,X2)),k2_funct_2(X1,X2)) = k6_relat_1(k2_relat_1(k2_funct_2(X1,X2)))
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_71]),c_0_68]),c_0_49]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)) = esk2_0
    | ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_62]),c_0_36]),c_0_26]),c_0_27]),c_0_25])])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(k2_funct_2(esk1_0,esk2_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_25]),c_0_36]),c_0_26]),c_0_27])])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_52])).

cnf(c_0_80,negated_conjecture,
    ( k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0)) = k6_relat_1(esk1_0)
    | ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_36]),c_0_26]),c_0_27]),c_0_25])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_57]),c_0_58])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_62]),c_0_36]),c_0_26]),c_0_27]),c_0_25])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_65]),c_0_36]),c_0_26]),c_0_27]),c_0_25])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_63]),c_0_36]),c_0_26]),c_0_27]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 0.21/0.39  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.39  fof(t87_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),k6_partfun1(X1))=>r2_relset_1(X1,X1,X3,k2_funct_2(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 0.21/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.21/0.39  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.21/0.39  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.21/0.39  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.21/0.39  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.21/0.39  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.21/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.21/0.39  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.21/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.21/0.39  fof(c_0_15, plain, ![X20, X21, X22]:(((v1_funct_1(X22)|(~v1_funct_1(X22)|~v3_funct_2(X22,X20,X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v2_funct_1(X22)|(~v1_funct_1(X22)|~v3_funct_2(X22,X20,X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(v2_funct_2(X22,X21)|(~v1_funct_1(X22)|~v3_funct_2(X22,X20,X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.21/0.39  fof(c_0_16, negated_conjecture, ((((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&v3_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.39  fof(c_0_17, plain, ![X12, X13, X14]:((v4_relat_1(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))&(v5_relat_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  fof(c_0_18, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.39  fof(c_0_19, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.39  fof(c_0_20, plain, ![X36, X37, X38]:(~v1_funct_1(X37)|~v1_funct_2(X37,X36,X36)|~v3_funct_2(X37,X36,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))|(~v1_funct_1(X38)|~v1_funct_2(X38,X36,X36)|~v3_funct_2(X38,X36,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X36)))|(~r2_relset_1(X36,X36,k1_partfun1(X36,X36,X36,X36,X37,X38),k6_partfun1(X36))|r2_relset_1(X36,X36,X38,k2_funct_2(X36,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_funct_2])])])).
% 0.21/0.39  fof(c_0_21, plain, ![X35]:k6_partfun1(X35)=k6_relat_1(X35), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.21/0.39  fof(c_0_22, plain, ![X33, X34]:(~v1_funct_1(X34)|~v1_funct_2(X34,X33,X33)|~v3_funct_2(X34,X33,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33)))|k2_funct_2(X33,X34)=k2_funct_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.21/0.39  fof(c_0_23, plain, ![X23, X24]:((~v2_funct_2(X24,X23)|k2_relat_1(X24)=X23|(~v1_relat_1(X24)|~v5_relat_1(X24,X23)))&(k2_relat_1(X24)!=X23|v2_funct_2(X24,X23)|(~v1_relat_1(X24)|~v5_relat_1(X24,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.21/0.39  cnf(c_0_24, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (v3_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_28, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_29, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_30, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_31, plain, (r2_relset_1(X2,X2,X3,k2_funct_2(X2,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X2)|~v3_funct_2(X3,X2,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X2,X2,X2,X1,X3),k6_partfun1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_32, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  fof(c_0_33, plain, ![X27, X28, X29, X30, X31, X32]:(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_partfun1(X27,X28,X29,X30,X31,X32)=k5_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.21/0.39  fof(c_0_34, plain, ![X11]:((k5_relat_1(X11,k2_funct_1(X11))=k6_relat_1(k1_relat_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(k5_relat_1(k2_funct_1(X11),X11)=k6_relat_1(k2_relat_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.21/0.39  cnf(c_0_35, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_37, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (v2_funct_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (v5_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_30])])).
% 0.21/0.39  cnf(c_0_41, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_42, plain, ![X25, X26]:((((v1_funct_1(k2_funct_2(X25,X26))|(~v1_funct_1(X26)|~v1_funct_2(X26,X25,X25)|~v3_funct_2(X26,X25,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25)))))&(v1_funct_2(k2_funct_2(X25,X26),X25,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,X25,X25)|~v3_funct_2(X26,X25,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))))))&(v3_funct_2(k2_funct_2(X25,X26),X25,X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,X25,X25)|~v3_funct_2(X26,X25,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25))))))&(m1_subset_1(k2_funct_2(X25,X26),k1_zfmisc_1(k2_zfmisc_1(X25,X25)))|(~v1_funct_1(X26)|~v1_funct_2(X26,X25,X25)|~v3_funct_2(X26,X25,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.21/0.39  cnf(c_0_43, plain, (r2_relset_1(X2,X2,X3,k2_funct_2(X2,X1))|~v1_funct_1(X3)|~v1_funct_1(X1)|~v3_funct_2(X3,X2,X2)|~v3_funct_2(X1,X2,X2)|~v1_funct_2(X3,X2,X2)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X2,X2,X2,X1,X3),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.39  cnf(c_0_44, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_45, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (k2_funct_1(esk2_0)=k2_funct_2(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_36]), c_0_26]), c_0_27])])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (k2_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (v2_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_26]), c_0_27])])).
% 0.21/0.39  cnf(c_0_49, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  fof(c_0_50, plain, ![X15, X16, X17, X18]:((~r2_relset_1(X15,X16,X17,X18)|X17=X18|(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(X17!=X18|r2_relset_1(X15,X16,X17,X18)|(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.21/0.39  cnf(c_0_51, plain, (r2_relset_1(X1,X1,X2,k2_funct_2(X1,X3))|~v1_funct_2(X2,X1,X1)|~v1_funct_2(X3,X1,X1)|~v3_funct_2(X2,X1,X1)|~v3_funct_2(X3,X1,X1)|~r2_relset_1(X1,X1,k5_relat_1(X3,X2),k6_relat_1(X1))|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_27]), c_0_40])])).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, (v1_funct_1(k2_funct_2(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_25]), c_0_36]), c_0_26]), c_0_27])])).
% 0.21/0.39  cnf(c_0_54, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.39  fof(c_0_55, plain, ![X19]:m1_subset_1(k6_relat_1(X19),k1_zfmisc_1(k2_zfmisc_1(X19,X19))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (r2_relset_1(X1,X1,esk2_0,k2_funct_2(X1,k2_funct_2(esk1_0,esk2_0)))|~v1_funct_2(k2_funct_2(esk1_0,esk2_0),X1,X1)|~v1_funct_2(esk2_0,X1,X1)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),X1,X1)|~v3_funct_2(esk2_0,X1,X1)|~r2_relset_1(X1,X1,k6_relat_1(esk1_0),k6_relat_1(X1))|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_27]), c_0_53])])).
% 0.21/0.39  cnf(c_0_57, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_54])).
% 0.21/0.39  cnf(c_0_58, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_60, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)))|~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36]), c_0_26]), c_0_25]), c_0_58])])).
% 0.21/0.39  cnf(c_0_62, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_63, plain, (v3_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_32]), c_0_32])).
% 0.21/0.39  cnf(c_0_65, plain, (v1_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0))=esk2_0|~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~m1_subset_1(k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_25])])).
% 0.21/0.39  cnf(c_0_67, plain, (v2_funct_2(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_62]), c_0_49]), c_0_63])).
% 0.21/0.39  cnf(c_0_68, plain, (v1_relat_1(k2_funct_2(X1,X2))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_62]), c_0_30])])).
% 0.21/0.39  cnf(c_0_69, plain, (v5_relat_1(k2_funct_2(X1,X2),X1)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_28, c_0_62])).
% 0.21/0.39  cnf(c_0_70, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0))|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_44]), c_0_27]), c_0_53]), c_0_25])])).
% 0.21/0.39  cnf(c_0_71, plain, (k2_funct_2(X1,k2_funct_2(X1,X2))=k2_funct_1(k2_funct_2(X1,X2))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_62]), c_0_49]), c_0_63]), c_0_65])).
% 0.21/0.39  cnf(c_0_72, plain, (v2_funct_1(k2_funct_2(X1,X2))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_62]), c_0_49]), c_0_63])).
% 0.21/0.39  cnf(c_0_73, negated_conjecture, (k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0))=esk2_0|~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_62]), c_0_53])])).
% 0.21/0.39  cnf(c_0_74, plain, (k2_relat_1(k2_funct_2(X1,X2))=X1|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_67]), c_0_68]), c_0_69])).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0))|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_44]), c_0_53]), c_0_27]), c_0_25])])).
% 0.21/0.39  cnf(c_0_76, plain, (k5_relat_1(k2_funct_2(X1,k2_funct_2(X1,X2)),k2_funct_2(X1,X2))=k6_relat_1(k2_relat_1(k2_funct_2(X1,X2)))|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_71]), c_0_68]), c_0_49]), c_0_72])).
% 0.21/0.39  cnf(c_0_77, negated_conjecture, (k2_funct_2(esk1_0,k2_funct_2(esk1_0,esk2_0))=esk2_0|~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_62]), c_0_36]), c_0_26]), c_0_27]), c_0_25])])).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (k2_relat_1(k2_funct_2(esk1_0,esk2_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_25]), c_0_36]), c_0_26]), c_0_27])])).
% 0.21/0.39  cnf(c_0_79, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[c_0_75, c_0_52])).
% 0.21/0.39  cnf(c_0_80, negated_conjecture, (k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0))=k6_relat_1(esk1_0)|~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_36]), c_0_26]), c_0_27]), c_0_25])])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~m1_subset_1(k2_funct_2(esk1_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_57]), c_0_58])])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (~v1_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)|~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_62]), c_0_36]), c_0_26]), c_0_27]), c_0_25])])).
% 0.21/0.39  cnf(c_0_84, negated_conjecture, (~v3_funct_2(k2_funct_2(esk1_0,esk2_0),esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_65]), c_0_36]), c_0_26]), c_0_27]), c_0_25])])).
% 0.21/0.39  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_63]), c_0_36]), c_0_26]), c_0_27]), c_0_25])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 86
% 0.21/0.39  # Proof object clause steps            : 57
% 0.21/0.39  # Proof object formula steps           : 29
% 0.21/0.39  # Proof object conjectures             : 32
% 0.21/0.39  # Proof object clause conjectures      : 29
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 23
% 0.21/0.39  # Proof object initial formulas used   : 14
% 0.21/0.39  # Proof object generating inferences   : 30
% 0.21/0.39  # Proof object simplifying inferences  : 95
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 14
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 27
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 25
% 0.21/0.39  # Processed clauses                    : 192
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 21
% 0.21/0.39  # ...remaining for further processing  : 171
% 0.21/0.39  # Other redundant clauses eliminated   : 2
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 10
% 0.21/0.39  # Backward-rewritten                   : 2
% 0.21/0.39  # Generated clauses                    : 286
% 0.21/0.39  # ...of the previous two non-trivial   : 234
% 0.21/0.39  # Contextual simplify-reflections      : 49
% 0.21/0.39  # Paramodulations                      : 284
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 2
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 132
% 0.21/0.39  #    Positive orientable unit clauses  : 40
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 91
% 0.21/0.39  # Current number of unprocessed clauses: 92
% 0.21/0.39  # ...number of literals in the above   : 721
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 38
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 4241
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 551
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 80
% 0.21/0.39  # Unit Clause-clause subsumption calls : 34
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 23
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 11420
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.047 s
% 0.21/0.39  # System time              : 0.003 s
% 0.21/0.39  # Total time               : 0.050 s
% 0.21/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
