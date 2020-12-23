%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:06 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  103 (16177 expanded)
%              Number of clauses        :   68 (5476 expanded)
%              Number of leaves         :   17 (3960 expanded)
%              Depth                    :   19
%              Number of atoms          :  363 (79783 expanded)
%              Number of equality atoms :   84 (4794 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t54_relset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
         => ( ! [X4] :
                ( r2_hidden(X4,X1)
               => k11_relat_1(X2,X4) = k11_relat_1(X3,X4) )
           => r2_relset_1(X1,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk3_0,esk3_0)
    & v3_funct_2(esk4_0,esk3_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    & ( ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))
      | ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0),esk4_0),k6_partfun1(esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X18] :
      ( ( k2_relat_1(X18) = k1_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_relat_1(X18) = k2_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v3_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X53,X54] :
      ( ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X53,X53)
      | ~ v3_funct_2(X54,X53,X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X53,X53)))
      | k2_funct_2(X53,X54) = k2_funct_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_28,plain,(
    ! [X44,X45] :
      ( ( v1_funct_1(k2_funct_2(X44,X45))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X44,X44)
        | ~ v3_funct_2(X45,X44,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))) )
      & ( v1_funct_2(k2_funct_2(X44,X45),X44,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X44,X44)
        | ~ v3_funct_2(X45,X44,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))) )
      & ( v3_funct_2(k2_funct_2(X44,X45),X44,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X44,X44)
        | ~ v3_funct_2(X45,X44,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))) )
      & ( m1_subset_1(k2_funct_2(X44,X45),k1_zfmisc_1(k2_zfmisc_1(X44,X44)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X44,X44)
        | ~ v3_funct_2(X45,X44,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_29,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_23])])).

cnf(c_0_32,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X47,X48,X49,X50,X51,X52] :
      ( ~ v1_funct_1(X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k1_partfun1(X47,X48,X49,X50,X51,X52) = k5_relat_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_35,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) = k2_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_36,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])]),c_0_31])])).

cnf(c_0_39,negated_conjecture,
    ( k2_funct_1(esk4_0) = k2_funct_2(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_26]),c_0_23])])).

cnf(c_0_40,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_42,plain,(
    ! [X55,X56,X57] :
      ( ( k5_relat_1(X57,k2_funct_1(X57)) = k6_partfun1(X55)
        | X56 = k1_xboole_0
        | k2_relset_1(X55,X56,X57) != X56
        | ~ v2_funct_1(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( k5_relat_1(k2_funct_1(X57),X57) = k6_partfun1(X56)
        | X56 = k1_xboole_0
        | k2_relset_1(X55,X56,X57) != X56
        | ~ v2_funct_1(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

cnf(c_0_43,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X37 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != k1_xboole_0
        | v1_funct_2(X37,X35,X36)
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_45,plain,
    ( v1_funct_2(k2_funct_2(X1,X2),X1,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_25]),c_0_26]),c_0_23])])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k2_funct_2(esk3_0,esk4_0)) = k2_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_49,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(esk2_3(X28,X29,X30),X28)
        | r2_relset_1(X28,X28,X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))) )
      & ( k11_relat_1(X29,esk2_3(X28,X29,X30)) != k11_relat_1(X30,esk2_3(X28,X29,X30))
        | r2_relset_1(X28,X28,X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).

cnf(c_0_50,negated_conjecture,
    ( k1_partfun1(X1,X2,esk3_0,esk3_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_26])])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_25]),c_0_26]),c_0_23])])).

cnf(c_0_52,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk3_0,esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_54,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(k2_funct_2(esk3_0,esk4_0),esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_25]),c_0_26]),c_0_23])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relset_1(esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0)) = k2_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_57,plain,
    ( r2_relset_1(X2,X2,X1,X3)
    | k11_relat_1(X1,esk2_3(X2,X1,X3)) != k11_relat_1(X3,esk2_3(X2,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X46] :
      ( v1_partfun1(k6_partfun1(X46),X46)
      & m1_subset_1(k6_partfun1(X46),k1_zfmisc_1(k2_zfmisc_1(X46,X46))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))
    | ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0),esk4_0),k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0),esk4_0) = k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_51])])).

cnf(c_0_61,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0) = k6_partfun1(esk3_0)
    | esk3_0 = k1_xboole_0
    | k2_relat_1(esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_39]),c_0_33]),c_0_31]),c_0_26]),c_0_23])])).

cnf(c_0_62,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_47])])).

cnf(c_0_63,plain,
    ( r2_relset_1(X1,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))
    | ~ r2_relset_1(esk3_0,esk3_0,k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0),k6_partfun1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0) = k6_partfun1(esk3_0)
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( r2_relset_1(X1,X1,k6_partfun1(X1),k6_partfun1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k1_partfun1(X1,X2,esk3_0,esk3_0,X3,k2_funct_2(esk3_0,esk4_0)) = k5_relat_1(X3,k2_funct_2(esk3_0,esk4_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_47]),c_0_51])])).

cnf(c_0_69,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_71,negated_conjecture,
    ( k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)) = k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_23]),c_0_26])])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0)) = k6_partfun1(esk3_0)
    | esk3_0 = k1_xboole_0
    | k2_relat_1(esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_53]),c_0_33]),c_0_31]),c_0_26]),c_0_23])]),c_0_39])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_relset_1(esk3_0,esk3_0,k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0)) = k6_partfun1(esk3_0)
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_62])).

fof(c_0_75,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ( v1_funct_1(k1_partfun1(X38,X39,X40,X41,X42,X43))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( m1_subset_1(k1_partfun1(X38,X39,X40,X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X38,X41)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_67])])).

cnf(c_0_77,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_funct_2(k1_xboole_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k2_funct_2(k1_xboole_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_76]),c_0_76])).

fof(c_0_81,plain,(
    ! [X15,X16,X17] :
      ( ~ r2_hidden(X15,X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X17))
      | ~ v1_xboole_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_82,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_83,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_relset_1(X1,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,k2_funct_2(k1_xboole_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk4_0,k2_funct_2(k1_xboole_0,esk4_0)) = k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_80]),c_0_26])])).

cnf(c_0_87,negated_conjecture,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,esk4_0),esk4_0) = k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,plain,
    ( r2_relset_1(X1,X1,X2,k6_partfun1(X1))
    | r2_hidden(esk2_3(X1,X2,k6_partfun1(X1)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_64])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_80]),c_0_85]),c_0_26])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_78]),c_0_87]),c_0_79])])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0))
    | r2_hidden(esk2_3(k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0))
    | r2_hidden(esk2_3(k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_92])).

fof(c_0_96,plain,(
    ! [X7] :
      ( m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))
      & v1_xboole_0(esk1_1(X7)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0))
    | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_71]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_98,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_95])).

cnf(c_0_100,plain,
    ( v1_xboole_0(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_102,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_100,c_0_101]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.46/0.66  # and selection function SelectCQArNTNpEqFirst.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.029 s
% 0.46/0.66  # Presaturation interreduction done
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 0.46/0.66  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.46/0.66  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.46/0.66  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.46/0.66  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.46/0.66  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.46/0.66  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.46/0.66  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.46/0.66  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.46/0.66  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.46/0.66  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.46/0.66  fof(t54_relset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(![X4]:(r2_hidden(X4,X1)=>k11_relat_1(X2,X4)=k11_relat_1(X3,X4))=>r2_relset_1(X1,X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 0.46/0.66  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.46/0.66  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.46/0.66  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.46/0.66  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.46/0.66  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.46/0.66  fof(c_0_17, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.46/0.66  fof(c_0_18, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.46/0.66  fof(c_0_19, negated_conjecture, ((((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&v3_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))|~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0),esk4_0),k6_partfun1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.46/0.66  fof(c_0_20, plain, ![X32, X33, X34]:(((v1_funct_1(X34)|(~v1_funct_1(X34)|~v3_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v2_funct_1(X34)|(~v1_funct_1(X34)|~v3_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(v2_funct_2(X34,X33)|(~v1_funct_1(X34)|~v3_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.46/0.66  fof(c_0_21, plain, ![X18]:((k2_relat_1(X18)=k1_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k1_relat_1(X18)=k2_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.46/0.66  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.66  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.66  cnf(c_0_24, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.66  cnf(c_0_25, negated_conjecture, (v3_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.66  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.66  fof(c_0_27, plain, ![X53, X54]:(~v1_funct_1(X54)|~v1_funct_2(X54,X53,X53)|~v3_funct_2(X54,X53,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X53,X53)))|k2_funct_2(X53,X54)=k2_funct_1(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.46/0.66  fof(c_0_28, plain, ![X44, X45]:((((v1_funct_1(k2_funct_2(X44,X45))|(~v1_funct_1(X45)|~v1_funct_2(X45,X44,X44)|~v3_funct_2(X45,X44,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))))&(v1_funct_2(k2_funct_2(X44,X45),X44,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,X44,X44)|~v3_funct_2(X45,X44,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))))))&(v3_funct_2(k2_funct_2(X44,X45),X44,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,X44,X44)|~v3_funct_2(X45,X44,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44))))))&(m1_subset_1(k2_funct_2(X44,X45),k1_zfmisc_1(k2_zfmisc_1(X44,X44)))|(~v1_funct_1(X45)|~v1_funct_2(X45,X44,X44)|~v3_funct_2(X45,X44,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X44,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.46/0.66  cnf(c_0_29, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.66  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.46/0.66  cnf(c_0_31, negated_conjecture, (v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_23])])).
% 0.46/0.66  cnf(c_0_32, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.66  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.66  fof(c_0_34, plain, ![X47, X48, X49, X50, X51, X52]:(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|k1_partfun1(X47,X48,X49,X50,X51,X52)=k5_relat_1(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.46/0.66  fof(c_0_35, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_relset_1(X25,X26,X27)=k2_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.46/0.66  fof(c_0_36, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.46/0.66  cnf(c_0_37, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_38, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])]), c_0_31])])).
% 0.46/0.66  cnf(c_0_39, negated_conjecture, (k2_funct_1(esk4_0)=k2_funct_2(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_26]), c_0_23])])).
% 0.46/0.66  cnf(c_0_40, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.46/0.66  cnf(c_0_41, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  fof(c_0_42, plain, ![X55, X56, X57]:((k5_relat_1(X57,k2_funct_1(X57))=k6_partfun1(X55)|X56=k1_xboole_0|(k2_relset_1(X55,X56,X57)!=X56|~v2_funct_1(X57))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(k5_relat_1(k2_funct_1(X57),X57)=k6_partfun1(X56)|X56=k1_xboole_0|(k2_relset_1(X55,X56,X57)!=X56|~v2_funct_1(X57))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.46/0.66  cnf(c_0_43, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.46/0.66  fof(c_0_44, plain, ![X35, X36, X37]:((((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&((~v1_funct_2(X37,X35,X36)|X37=k1_xboole_0|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X37!=k1_xboole_0|v1_funct_2(X37,X35,X36)|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.46/0.66  cnf(c_0_45, plain, (v1_funct_2(k2_funct_2(X1,X2),X1,X1)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_46, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.46/0.66  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_funct_2(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_25]), c_0_26]), c_0_23])])).
% 0.46/0.66  cnf(c_0_48, negated_conjecture, (k1_relat_1(k2_funct_2(esk3_0,esk4_0))=k2_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.46/0.66  fof(c_0_49, plain, ![X28, X29, X30]:((r2_hidden(esk2_3(X28,X29,X30),X28)|r2_relset_1(X28,X28,X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))))&(k11_relat_1(X29,esk2_3(X28,X29,X30))!=k11_relat_1(X30,esk2_3(X28,X29,X30))|r2_relset_1(X28,X28,X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X28)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relset_1])])])])])).
% 0.46/0.66  cnf(c_0_50, negated_conjecture, (k1_partfun1(X1,X2,esk3_0,esk3_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_26])])).
% 0.46/0.66  cnf(c_0_51, negated_conjecture, (v1_funct_1(k2_funct_2(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_33]), c_0_25]), c_0_26]), c_0_23])])).
% 0.46/0.66  cnf(c_0_52, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.46/0.66  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk3_0,esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 0.46/0.66  cnf(c_0_54, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.46/0.66  cnf(c_0_55, negated_conjecture, (v1_funct_2(k2_funct_2(esk3_0,esk4_0),esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_33]), c_0_25]), c_0_26]), c_0_23])])).
% 0.46/0.66  cnf(c_0_56, negated_conjecture, (k1_relset_1(esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0))=k2_relat_1(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.46/0.66  cnf(c_0_57, plain, (r2_relset_1(X2,X2,X1,X3)|k11_relat_1(X1,esk2_3(X2,X1,X3))!=k11_relat_1(X3,esk2_3(X2,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.46/0.66  fof(c_0_58, plain, ![X46]:(v1_partfun1(k6_partfun1(X46),X46)&m1_subset_1(k6_partfun1(X46),k1_zfmisc_1(k2_zfmisc_1(X46,X46)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.46/0.66  cnf(c_0_59, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))|~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0),esk4_0),k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.66  cnf(c_0_60, negated_conjecture, (k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,k2_funct_2(esk3_0,esk4_0),esk4_0)=k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_47]), c_0_51])])).
% 0.46/0.66  cnf(c_0_61, negated_conjecture, (k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0)=k6_partfun1(esk3_0)|esk3_0=k1_xboole_0|k2_relat_1(esk4_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_39]), c_0_33]), c_0_31]), c_0_26]), c_0_23])])).
% 0.46/0.66  cnf(c_0_62, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_47])])).
% 0.46/0.66  cnf(c_0_63, plain, (r2_relset_1(X1,X1,X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(er,[status(thm)],[c_0_57])).
% 0.46/0.66  cnf(c_0_64, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.46/0.66  cnf(c_0_65, negated_conjecture, (~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))|~r2_relset_1(esk3_0,esk3_0,k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0),k6_partfun1(esk3_0))), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.46/0.66  cnf(c_0_66, negated_conjecture, (k5_relat_1(k2_funct_2(esk3_0,esk4_0),esk4_0)=k6_partfun1(esk3_0)|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.46/0.66  cnf(c_0_67, plain, (r2_relset_1(X1,X1,k6_partfun1(X1),k6_partfun1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.46/0.66  cnf(c_0_68, negated_conjecture, (k1_partfun1(X1,X2,esk3_0,esk3_0,X3,k2_funct_2(esk3_0,esk4_0))=k5_relat_1(X3,k2_funct_2(esk3_0,esk4_0))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_47]), c_0_51])])).
% 0.46/0.66  cnf(c_0_69, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.46/0.66  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.46/0.66  cnf(c_0_71, negated_conjecture, (k1_partfun1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,k2_funct_2(esk3_0,esk4_0))=k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_23]), c_0_26])])).
% 0.46/0.66  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0))=k6_partfun1(esk3_0)|esk3_0=k1_xboole_0|k2_relat_1(esk4_0)!=esk3_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_53]), c_0_33]), c_0_31]), c_0_26]), c_0_23])]), c_0_39])).
% 0.46/0.66  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0|~r2_relset_1(esk3_0,esk3_0,k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0)),k6_partfun1(esk3_0))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.46/0.67  cnf(c_0_74, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_2(esk3_0,esk4_0))=k6_partfun1(esk3_0)|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_62])).
% 0.46/0.67  fof(c_0_75, plain, ![X38, X39, X40, X41, X42, X43]:((v1_funct_1(k1_partfun1(X38,X39,X40,X41,X42,X43))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&(m1_subset_1(k1_partfun1(X38,X39,X40,X41,X42,X43),k1_zfmisc_1(k2_zfmisc_1(X38,X41)))|(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.46/0.67  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_67])])).
% 0.46/0.67  cnf(c_0_77, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.46/0.67  cnf(c_0_78, negated_conjecture, (m1_subset_1(k2_funct_2(k1_xboole_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_76]), c_0_76]), c_0_76])).
% 0.46/0.67  cnf(c_0_79, negated_conjecture, (v1_funct_1(k2_funct_2(k1_xboole_0,esk4_0))), inference(rw,[status(thm)],[c_0_51, c_0_76])).
% 0.46/0.67  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_76]), c_0_76])).
% 0.46/0.67  fof(c_0_81, plain, ![X15, X16, X17]:(~r2_hidden(X15,X16)|~m1_subset_1(X16,k1_zfmisc_1(X17))|~v1_xboole_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.46/0.67  fof(c_0_82, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.46/0.67  cnf(c_0_83, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_relset_1(X1,X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.46/0.67  cnf(c_0_84, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,k2_funct_2(k1_xboole_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.46/0.67  cnf(c_0_85, negated_conjecture, (k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,esk4_0,k2_funct_2(k1_xboole_0,esk4_0))=k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76])).
% 0.46/0.67  cnf(c_0_86, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k1_xboole_0,k1_xboole_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_80]), c_0_26])])).
% 0.46/0.67  cnf(c_0_87, negated_conjecture, (k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,esk4_0),esk4_0)=k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76])).
% 0.46/0.67  cnf(c_0_88, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.46/0.67  cnf(c_0_89, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.46/0.67  cnf(c_0_90, plain, (r2_relset_1(X1,X1,X2,k6_partfun1(X1))|r2_hidden(esk2_3(X1,X2,k6_partfun1(X1)),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_83, c_0_64])).
% 0.46/0.67  cnf(c_0_91, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_80]), c_0_85]), c_0_26])])).
% 0.46/0.67  cnf(c_0_92, negated_conjecture, (m1_subset_1(k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_78]), c_0_87]), c_0_79])])).
% 0.46/0.67  cnf(c_0_93, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.46/0.67  cnf(c_0_94, negated_conjecture, (r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0))|r2_hidden(esk2_3(k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.46/0.67  cnf(c_0_95, negated_conjecture, (r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0))|r2_hidden(esk2_3(k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_92])).
% 0.46/0.67  fof(c_0_96, plain, ![X7]:(m1_subset_1(esk1_1(X7),k1_zfmisc_1(X7))&v1_xboole_0(esk1_1(X7))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.46/0.67  cnf(c_0_97, negated_conjecture, (~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0))|~r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_71]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76]), c_0_76])).
% 0.46/0.67  cnf(c_0_98, negated_conjecture, (r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(esk4_0,k2_funct_2(k1_xboole_0,esk4_0)),k6_partfun1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.46/0.67  cnf(c_0_99, negated_conjecture, (r2_relset_1(k1_xboole_0,k1_xboole_0,k5_relat_1(k2_funct_2(k1_xboole_0,esk4_0),esk4_0),k6_partfun1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_93, c_0_95])).
% 0.46/0.67  cnf(c_0_100, plain, (v1_xboole_0(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.46/0.67  cnf(c_0_101, negated_conjecture, (~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.46/0.67  cnf(c_0_102, plain, ($false), inference(sr,[status(thm)],[c_0_100, c_0_101]), ['proof']).
% 0.46/0.67  # SZS output end CNFRefutation
% 0.46/0.67  # Proof object total steps             : 103
% 0.46/0.67  # Proof object clause steps            : 68
% 0.46/0.67  # Proof object formula steps           : 35
% 0.46/0.67  # Proof object conjectures             : 46
% 0.46/0.67  # Proof object clause conjectures      : 43
% 0.46/0.67  # Proof object formula conjectures     : 3
% 0.46/0.67  # Proof object initial clauses used    : 25
% 0.46/0.67  # Proof object initial formulas used   : 17
% 0.46/0.67  # Proof object generating inferences   : 33
% 0.46/0.67  # Proof object simplifying inferences  : 93
% 0.46/0.67  # Training examples: 0 positive, 0 negative
% 0.46/0.67  # Parsed axioms                        : 19
% 0.46/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.67  # Initial clauses                      : 39
% 0.46/0.67  # Removed in clause preprocessing      : 1
% 0.46/0.67  # Initial clauses in saturation        : 38
% 0.46/0.67  # Processed clauses                    : 2340
% 0.46/0.67  # ...of these trivial                  : 42
% 0.46/0.67  # ...subsumed                          : 99
% 0.46/0.67  # ...remaining for further processing  : 2199
% 0.46/0.67  # Other redundant clauses eliminated   : 10
% 0.46/0.67  # Clauses deleted for lack of memory   : 0
% 0.46/0.67  # Backward-subsumed                    : 4
% 0.46/0.67  # Backward-rewritten                   : 258
% 0.46/0.67  # Generated clauses                    : 11176
% 0.46/0.67  # ...of the previous two non-trivial   : 11320
% 0.46/0.67  # Contextual simplify-reflections      : 5
% 0.46/0.67  # Paramodulations                      : 11164
% 0.46/0.67  # Factorizations                       : 0
% 0.46/0.67  # Equation resolutions                 : 11
% 0.46/0.67  # Propositional unsat checks           : 0
% 0.46/0.67  #    Propositional check models        : 0
% 0.46/0.67  #    Propositional check unsatisfiable : 0
% 0.46/0.67  #    Propositional clauses             : 0
% 0.46/0.67  #    Propositional clauses after purity: 0
% 0.46/0.67  #    Propositional unsat core size     : 0
% 0.46/0.67  #    Propositional preprocessing time  : 0.000
% 0.46/0.67  #    Propositional encoding time       : 0.000
% 0.46/0.67  #    Propositional solver time         : 0.000
% 0.46/0.67  #    Success case prop preproc time    : 0.000
% 0.46/0.67  #    Success case prop encoding time   : 0.000
% 0.46/0.67  #    Success case prop solver time     : 0.000
% 0.46/0.67  # Current number of processed clauses  : 1893
% 0.46/0.67  #    Positive orientable unit clauses  : 557
% 0.46/0.67  #    Positive unorientable unit clauses: 4
% 0.46/0.67  #    Negative unit clauses             : 1
% 0.46/0.67  #    Non-unit-clauses                  : 1331
% 0.46/0.67  # Current number of unprocessed clauses: 8921
% 0.46/0.67  # ...number of literals in the above   : 11236
% 0.46/0.67  # Current number of archived formulas  : 0
% 0.46/0.67  # Current number of archived clauses   : 302
% 0.46/0.67  # Clause-clause subsumption calls (NU) : 144283
% 0.46/0.67  # Rec. Clause-clause subsumption calls : 112766
% 0.46/0.67  # Non-unit clause-clause subsumptions  : 100
% 0.46/0.67  # Unit Clause-clause subsumption calls : 81291
% 0.46/0.67  # Rewrite failures with RHS unbound    : 27
% 0.46/0.67  # BW rewrite match attempts            : 54829
% 0.46/0.67  # BW rewrite match successes           : 62
% 0.46/0.67  # Condensation attempts                : 0
% 0.46/0.67  # Condensation successes               : 0
% 0.46/0.67  # Termbank termtop insertions          : 472040
% 0.46/0.67  
% 0.46/0.67  # -------------------------------------------------
% 0.46/0.67  # User time                : 0.293 s
% 0.46/0.67  # System time              : 0.017 s
% 0.46/0.67  # Total time               : 0.310 s
% 0.46/0.67  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
