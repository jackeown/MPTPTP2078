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
% DateTime   : Thu Dec  3 11:06:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 (15956 expanded)
%              Number of clauses        :   81 (5727 expanded)
%              Number of leaves         :   19 (3953 expanded)
%              Depth                    :   20
%              Number of atoms          :  427 (72080 expanded)
%              Number of equality atoms :   77 (5185 expanded)
%              Maximal formula depth    :   13 (   5 average)
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

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t54_relset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
         => ( ! [X4] :
                ( r2_hidden(X4,X1)
               => k11_relat_1(X2,X4) = k11_relat_1(X3,X4) )
           => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_20,plain,(
    ! [X54,X55,X56] :
      ( ( k5_relat_1(X56,k2_funct_1(X56)) = k6_partfun1(X54)
        | X55 = k1_xboole_0
        | k2_relset_1(X54,X55,X56) != X55
        | ~ v2_funct_1(X56)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( k5_relat_1(k2_funct_1(X56),X56) = k6_partfun1(X55)
        | X55 = k1_xboole_0
        | k2_relset_1(X54,X55,X56) != X55
        | ~ v2_funct_1(X56)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_21,plain,(
    ! [X53] : k6_partfun1(X53) = k6_relat_1(X53) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v3_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v2_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v3_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v2_funct_2(X34,X33)
        | ~ v1_funct_1(X34)
        | ~ v3_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk2_0,esk2_0)
    & v3_funct_2(esk3_0,esk2_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))
      | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ( v4_relat_1(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v5_relat_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_26,plain,(
    ! [X43,X44] :
      ( ( v1_funct_1(k2_funct_2(X43,X44))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X43,X43)
        | ~ v3_funct_2(X44,X43,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43))) )
      & ( v1_funct_2(k2_funct_2(X43,X44),X43,X43)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X43,X43)
        | ~ v3_funct_2(X44,X43,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43))) )
      & ( v3_funct_2(k2_funct_2(X43,X44),X43,X43)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X43,X43)
        | ~ v3_funct_2(X44,X43,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43))) )
      & ( m1_subset_1(k2_funct_2(X43,X44),k1_zfmisc_1(k2_zfmisc_1(X43,X43)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X43,X43)
        | ~ v3_funct_2(X44,X43,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_27,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k2_relset_1(X20,X21,X22) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_30,plain,(
    ! [X35,X36] :
      ( ( ~ v2_funct_2(X36,X35)
        | k2_relat_1(X36) = X35
        | ~ v1_relat_1(X36)
        | ~ v5_relat_1(X36,X35) )
      & ( k2_relat_1(X36) != X35
        | v2_funct_2(X36,X35)
        | ~ v1_relat_1(X36)
        | ~ v5_relat_1(X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_31,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v3_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X51,X52] :
      ( ~ v1_funct_1(X52)
      | ~ v1_funct_2(X52,X51,X51)
      | ~ v3_funct_2(X52,X51,X51)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X51)))
      | k2_funct_2(X51,X52) = k2_funct_1(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_39,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_partfun1(X45,X46,X47,X48,X49,X50) = k5_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_40,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_43,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( v2_funct_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_48,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_50,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_28]),c_0_28])).

cnf(c_0_52,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_54,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | k2_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( k2_funct_1(esk3_0) = k2_funct_2(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_57,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_58,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_59,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_33]),c_0_53]),c_0_34])])).

cnf(c_0_62,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0) = k6_relat_1(esk2_0)
    | esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,X1,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_33])])).

cnf(c_0_63,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_28])).

fof(c_0_64,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_52]),c_0_53]),c_0_33]),c_0_34])])).

cnf(c_0_68,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0) = k6_relat_1(esk2_0)
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_41]),c_0_34])])).

cnf(c_0_69,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_43])])).

fof(c_0_70,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ r2_relset_1(X23,X24,X25,X26)
        | X25 = X26
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != X26
        | r2_relset_1(X23,X24,X25,X26)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_73,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(esk1_3(X28,X29,X30),X28)
        | r2_relset_1(X28,X28,X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))) )
      & ( k11_relat_1(X29,esk1_3(X28,X29,X30)) != k11_relat_1(X30,esk1_3(X28,X29,X30))
        | r2_relset_1(X28,X28,X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)) = k6_relat_1(X1)
    | esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,X1,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_55]),c_0_56]),c_0_57]),c_0_33])])).

cnf(c_0_76,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_77,plain,(
    ! [X27] : m1_subset_1(k6_relat_1(X27),k1_zfmisc_1(k2_zfmisc_1(X27,X27))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_relset_1(X1,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,X1,esk2_0)
    | ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))
    | ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(X1),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( r2_relset_1(X1,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,X1,esk2_0)
    | ~ r2_relset_1(esk2_0,esk2_0,k6_relat_1(X1),k6_relat_1(esk2_0))
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

fof(c_0_86,plain,(
    ! [X37,X38,X39,X40,X41,X42] :
      ( ( v1_funct_1(k1_partfun1(X37,X38,X39,X40,X41,X42))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( m1_subset_1(k1_partfun1(X37,X38,X39,X40,X41,X42),k1_zfmisc_1(k2_zfmisc_1(X37,X40)))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_87,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_88,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_81]),c_0_41]),c_0_34]),c_0_82])])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_91,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_41]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_52])).

cnf(c_0_95,plain,
    ( X1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_72])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_93]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_34]),c_0_33])])).

cnf(c_0_98,plain,
    ( X1 = k6_relat_1(k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_82])).

cnf(c_0_99,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_97,c_0_93])).

cnf(c_0_101,plain,
    ( k6_relat_1(k1_xboole_0) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_72])).

cnf(c_0_102,plain,
    ( X1 = esk3_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_99]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_99]),c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk3_0,k2_funct_2(k1_xboole_0,esk3_0)),esk3_0)
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk3_0),esk3_0),esk3_0)
    | ~ m1_subset_1(k2_funct_2(k1_xboole_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_101]),c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_101]),c_0_93]),c_0_93]),c_0_93]),c_0_99]),c_0_99]),c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k5_relat_1(X1,esk3_0) = esk3_0
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_1(k2_funct_2(k1_xboole_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_93])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_34]),c_0_33])])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk3_0,k2_funct_2(k1_xboole_0,esk3_0)),esk3_0)
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,esk3_0)
    | ~ m1_subset_1(k2_funct_2(k1_xboole_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106])])).

cnf(c_0_109,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_99]),c_0_99])).

cnf(c_0_110,plain,
    ( k2_funct_2(k1_xboole_0,X1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ v3_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_90])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_93]),c_0_93]),c_0_99])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,esk3_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,k2_funct_2(k1_xboole_0,esk3_0)),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(k2_funct_2(k1_xboole_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_72])])).

cnf(c_0_113,plain,
    ( k2_funct_2(k1_xboole_0,X1) = esk3_0
    | ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ v3_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_99]),c_0_99])).

cnf(c_0_114,negated_conjecture,
    ( k5_relat_1(esk3_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_93]),c_0_93])).

cnf(c_0_116,negated_conjecture,
    ( v3_funct_2(esk3_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_93]),c_0_93])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114]),c_0_72]),c_0_72]),c_0_115]),c_0_116]),c_0_33])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_81]),c_0_99]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.029 s
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 0.20/0.46  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.20/0.46  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.46  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.20/0.46  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.46  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.46  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.20/0.46  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.46  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.20/0.46  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.20/0.46  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.46  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.46  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.46  fof(t54_relset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(![X4]:(r2_hidden(X4,X1)=>k11_relat_1(X2,X4)=k11_relat_1(X3,X4))=>r2_relset_1(X1,X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 0.20/0.46  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.20/0.46  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.46  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.20/0.46  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.20/0.46  fof(c_0_20, plain, ![X54, X55, X56]:((k5_relat_1(X56,k2_funct_1(X56))=k6_partfun1(X54)|X55=k1_xboole_0|(k2_relset_1(X54,X55,X56)!=X55|~v2_funct_1(X56))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&(k5_relat_1(k2_funct_1(X56),X56)=k6_partfun1(X55)|X55=k1_xboole_0|(k2_relset_1(X54,X55,X56)!=X55|~v2_funct_1(X56))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.20/0.46  fof(c_0_21, plain, ![X53]:k6_partfun1(X53)=k6_relat_1(X53), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.46  fof(c_0_22, plain, ![X32, X33, X34]:(((v1_funct_1(X34)|(~v1_funct_1(X34)|~v3_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v2_funct_1(X34)|(~v1_funct_1(X34)|~v3_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(v2_funct_2(X34,X33)|(~v1_funct_1(X34)|~v3_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.20/0.46  fof(c_0_23, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&v3_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.46  fof(c_0_24, plain, ![X17, X18, X19]:((v4_relat_1(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(v5_relat_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.46  fof(c_0_25, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.46  fof(c_0_26, plain, ![X43, X44]:((((v1_funct_1(k2_funct_2(X43,X44))|(~v1_funct_1(X44)|~v1_funct_2(X44,X43,X43)|~v3_funct_2(X44,X43,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43)))))&(v1_funct_2(k2_funct_2(X43,X44),X43,X43)|(~v1_funct_1(X44)|~v1_funct_2(X44,X43,X43)|~v3_funct_2(X44,X43,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43))))))&(v3_funct_2(k2_funct_2(X43,X44),X43,X43)|(~v1_funct_1(X44)|~v1_funct_2(X44,X43,X43)|~v3_funct_2(X44,X43,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43))))))&(m1_subset_1(k2_funct_2(X43,X44),k1_zfmisc_1(k2_zfmisc_1(X43,X43)))|(~v1_funct_1(X44)|~v1_funct_2(X44,X43,X43)|~v3_funct_2(X44,X43,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X43,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.20/0.46  cnf(c_0_27, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_28, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  fof(c_0_29, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k2_relset_1(X20,X21,X22)=k2_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.46  fof(c_0_30, plain, ![X35, X36]:((~v2_funct_2(X36,X35)|k2_relat_1(X36)=X35|(~v1_relat_1(X36)|~v5_relat_1(X36,X35)))&(k2_relat_1(X36)!=X35|v2_funct_2(X36,X35)|(~v1_relat_1(X36)|~v5_relat_1(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.20/0.46  cnf(c_0_31, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  cnf(c_0_32, negated_conjecture, (v3_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_35, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.46  cnf(c_0_36, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.46  fof(c_0_37, plain, ![X51, X52]:(~v1_funct_1(X52)|~v1_funct_2(X52,X51,X51)|~v3_funct_2(X52,X51,X51)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X51)))|k2_funct_2(X51,X52)=k2_funct_1(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_partfun1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  fof(c_0_39, plain, ![X45, X46, X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_partfun1(X45,X46,X47,X48,X49,X50)=k5_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.46  cnf(c_0_40, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_42, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.46  cnf(c_0_43, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.46  cnf(c_0_44, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (v2_funct_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.46  cnf(c_0_48, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.46  cnf(c_0_49, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_50, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.46  cnf(c_0_51, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_28]), c_0_28])).
% 0.20/0.46  cnf(c_0_52, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (v1_funct_1(k2_funct_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.46  cnf(c_0_54, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|k2_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43])])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (k2_funct_1(esk3_0)=k2_funct_2(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.46  cnf(c_0_58, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  fof(c_0_59, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.46  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk2_0,esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_33]), c_0_53]), c_0_34])])).
% 0.20/0.46  cnf(c_0_62, negated_conjecture, (k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0)=k6_relat_1(esk2_0)|esk2_0=k1_xboole_0|~v1_funct_2(esk3_0,X1,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_33])])).
% 0.20/0.46  cnf(c_0_63, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_58, c_0_28])).
% 0.20/0.46  fof(c_0_64, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.46  cnf(c_0_65, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.46  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_52]), c_0_53]), c_0_33]), c_0_34])])).
% 0.20/0.46  cnf(c_0_68, negated_conjecture, (k5_relat_1(k2_funct_2(esk2_0,esk3_0),esk3_0)=k6_relat_1(esk2_0)|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_41]), c_0_34])])).
% 0.20/0.46  cnf(c_0_69, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_43])])).
% 0.20/0.46  fof(c_0_70, plain, ![X23, X24, X25, X26]:((~r2_relset_1(X23,X24,X25,X26)|X25=X26|(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(X25!=X26|r2_relset_1(X23,X24,X25,X26)|(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.46  cnf(c_0_71, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.46  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.46  fof(c_0_73, plain, ![X28, X29, X30]:((r2_hidden(esk1_3(X28,X29,X30),X28)|r2_relset_1(X28,X28,X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))))&(k11_relat_1(X29,esk1_3(X28,X29,X30))!=k11_relat_1(X30,esk1_3(X28,X29,X30))|r2_relset_1(X28,X28,X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (esk2_0=k1_xboole_0|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0)),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_2(esk2_0,esk3_0))=k6_relat_1(X1)|esk2_0=k1_xboole_0|~v1_funct_2(esk3_0,X1,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_55]), c_0_56]), c_0_57]), c_0_33])])).
% 0.20/0.46  cnf(c_0_76, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.46  fof(c_0_77, plain, ![X27]:m1_subset_1(k6_relat_1(X27),k1_zfmisc_1(k2_zfmisc_1(X27,X27))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.20/0.46  cnf(c_0_78, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.46  cnf(c_0_79, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_relset_1(X1,X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk3_0,X1,esk2_0)|~r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))|~r2_relset_1(esk2_0,esk2_0,k6_relat_1(X1),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.46  cnf(c_0_81, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_76])).
% 0.20/0.46  cnf(c_0_82, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.46  cnf(c_0_83, plain, (r2_relset_1(X1,X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.46  cnf(c_0_84, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk3_0,X1,esk2_0)|~r2_relset_1(esk2_0,esk2_0,k6_relat_1(X1),k6_relat_1(esk2_0))|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.20/0.46  fof(c_0_86, plain, ![X37, X38, X39, X40, X41, X42]:((v1_funct_1(k1_partfun1(X37,X38,X39,X40,X41,X42))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(m1_subset_1(k1_partfun1(X37,X38,X39,X40,X41,X42),k1_zfmisc_1(k2_zfmisc_1(X37,X40)))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.20/0.46  cnf(c_0_87, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.46  cnf(c_0_88, plain, (r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.46  cnf(c_0_89, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(k2_funct_2(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_81]), c_0_41]), c_0_34]), c_0_82])])).
% 0.20/0.46  cnf(c_0_90, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.46  cnf(c_0_91, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.46  cnf(c_0_92, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.46  cnf(c_0_93, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_41]), c_0_32]), c_0_33]), c_0_34])])).
% 0.20/0.46  cnf(c_0_94, plain, (m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))), inference(spm,[status(thm)],[c_0_91, c_0_52])).
% 0.20/0.46  cnf(c_0_95, plain, (X1=k2_zfmisc_1(k1_xboole_0,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_92, c_0_72])).
% 0.20/0.46  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_93]), c_0_93])).
% 0.20/0.46  cnf(c_0_97, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_34]), c_0_33])])).
% 0.20/0.46  cnf(c_0_98, plain, (X1=k6_relat_1(k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_92, c_0_82])).
% 0.20/0.46  cnf(c_0_99, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,k1_xboole_0)=esk3_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.46  cnf(c_0_100, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_97, c_0_93])).
% 0.20/0.46  cnf(c_0_101, plain, (k6_relat_1(k1_xboole_0)=k2_zfmisc_1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_72])).
% 0.20/0.46  cnf(c_0_102, plain, (X1=esk3_0|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_99]), c_0_99])).
% 0.20/0.46  cnf(c_0_103, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_99]), c_0_99])).
% 0.20/0.46  cnf(c_0_104, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk3_0,k2_funct_2(k1_xboole_0,esk3_0)),esk3_0)|~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk3_0),esk3_0),esk3_0)|~m1_subset_1(k2_funct_2(k1_xboole_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_101]), c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_101]), c_0_93]), c_0_93]), c_0_93]), c_0_99]), c_0_99]), c_0_99])).
% 0.20/0.46  cnf(c_0_105, negated_conjecture, (k5_relat_1(X1,esk3_0)=esk3_0|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.20/0.46  cnf(c_0_106, negated_conjecture, (v1_funct_1(k2_funct_2(k1_xboole_0,esk3_0))), inference(rw,[status(thm)],[c_0_53, c_0_93])).
% 0.20/0.46  cnf(c_0_107, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_34]), c_0_33])])).
% 0.20/0.46  cnf(c_0_108, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk3_0,k2_funct_2(k1_xboole_0,esk3_0)),esk3_0)|~r2_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,esk3_0)|~m1_subset_1(k2_funct_2(k1_xboole_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_106])])).
% 0.20/0.46  cnf(c_0_109, plain, (r2_relset_1(k1_xboole_0,k1_xboole_0,X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_99]), c_0_99])).
% 0.20/0.46  cnf(c_0_110, plain, (k2_funct_2(k1_xboole_0,X1)=k2_zfmisc_1(k1_xboole_0,k1_xboole_0)|~v1_funct_2(X1,k1_xboole_0,k1_xboole_0)|~v3_funct_2(X1,k1_xboole_0,k1_xboole_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_95, c_0_90])).
% 0.20/0.46  cnf(c_0_111, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_93]), c_0_93]), c_0_99])).
% 0.20/0.46  cnf(c_0_112, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,esk3_0)|~m1_subset_1(k5_relat_1(esk3_0,k2_funct_2(k1_xboole_0,esk3_0)),k1_zfmisc_1(esk3_0))|~m1_subset_1(k2_funct_2(k1_xboole_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_72])])).
% 0.20/0.46  cnf(c_0_113, plain, (k2_funct_2(k1_xboole_0,X1)=esk3_0|~v1_funct_2(X1,k1_xboole_0,k1_xboole_0)|~v3_funct_2(X1,k1_xboole_0,k1_xboole_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_99]), c_0_99])).
% 0.20/0.46  cnf(c_0_114, negated_conjecture, (k5_relat_1(esk3_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_102, c_0_111])).
% 0.20/0.46  cnf(c_0_115, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_93]), c_0_93])).
% 0.20/0.46  cnf(c_0_116, negated_conjecture, (v3_funct_2(esk3_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_93]), c_0_93])).
% 0.20/0.46  cnf(c_0_117, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114]), c_0_72]), c_0_72]), c_0_115]), c_0_116]), c_0_33])])).
% 0.20/0.46  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_81]), c_0_99]), c_0_72])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 119
% 0.20/0.46  # Proof object clause steps            : 81
% 0.20/0.46  # Proof object formula steps           : 38
% 0.20/0.46  # Proof object conjectures             : 43
% 0.20/0.46  # Proof object clause conjectures      : 40
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 27
% 0.20/0.46  # Proof object initial formulas used   : 19
% 0.20/0.46  # Proof object generating inferences   : 39
% 0.20/0.46  # Proof object simplifying inferences  : 106
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 19
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 37
% 0.20/0.46  # Removed in clause preprocessing      : 2
% 0.20/0.46  # Initial clauses in saturation        : 35
% 0.20/0.46  # Processed clauses                    : 858
% 0.20/0.46  # ...of these trivial                  : 52
% 0.20/0.46  # ...subsumed                          : 300
% 0.20/0.46  # ...remaining for further processing  : 506
% 0.20/0.46  # Other redundant clauses eliminated   : 6
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 22
% 0.20/0.46  # Backward-rewritten                   : 253
% 0.20/0.46  # Generated clauses                    : 1882
% 0.20/0.46  # ...of the previous two non-trivial   : 1836
% 0.20/0.46  # Contextual simplify-reflections      : 22
% 0.20/0.46  # Paramodulations                      : 1875
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 7
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 227
% 0.20/0.46  #    Positive orientable unit clauses  : 29
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 1
% 0.20/0.46  #    Non-unit-clauses                  : 197
% 0.20/0.46  # Current number of unprocessed clauses: 842
% 0.20/0.46  # ...number of literals in the above   : 5068
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 276
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 18529
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 5679
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 344
% 0.20/0.46  # Unit Clause-clause subsumption calls : 7076
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 906
% 0.20/0.46  # BW rewrite match successes           : 4
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 48017
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.108 s
% 0.20/0.46  # System time              : 0.007 s
% 0.20/0.46  # Total time               : 0.115 s
% 0.20/0.46  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
