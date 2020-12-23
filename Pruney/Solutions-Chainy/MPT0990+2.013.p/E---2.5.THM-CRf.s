%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:00 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  129 (2455 expanded)
%              Number of clauses        :   88 ( 911 expanded)
%              Number of leaves         :   20 ( 572 expanded)
%              Depth                    :   18
%              Number of atoms          :  487 (18049 expanded)
%              Number of equality atoms :  129 (5620 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t24_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))
           => k2_relset_1(X1,X2,X3) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t30_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
              & k2_relset_1(X1,X2,X4) = X2 )
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | ( v2_funct_1(X4)
                & v2_funct_1(X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

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

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t64_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X2) = k1_relat_1(X1)
              & k5_relat_1(X2,X1) = k6_relat_1(k2_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
                & v2_funct_1(X3) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_funct_2])).

fof(c_0_21,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( v1_funct_1(k1_partfun1(X34,X35,X36,X37,X38,X39))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( m1_subset_1(k1_partfun1(X34,X35,X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(X34,X37)))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))
    & v2_funct_1(esk3_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk4_0 != k2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | ~ v1_funct_1(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_partfun1(X40,X41,X42,X43,X44,X45) = k5_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,X47,X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X48,X47)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
      | ~ r2_relset_1(X48,X48,k1_partfun1(X48,X47,X47,X48,X50,X49),k6_partfun1(X48))
      | k2_relset_1(X47,X48,X49) = X48 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

fof(c_0_28,plain,(
    ! [X46] : k6_partfun1(X46) = k6_relat_1(X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_partfun1(X1,X2,X3,X4,X5,esk4_0) = k5_relat_1(X5,esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_42,plain,(
    ! [X51,X52,X53,X54,X55] :
      ( ( v2_funct_1(X54)
        | X53 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X55)
        | X53 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X54)
        | X52 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( v2_funct_1(X55)
        | X52 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))
        | k2_relset_1(X51,X52,X54) != X52
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

fof(c_0_43,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ r2_relset_1(X29,X30,X31,X32)
        | X31 = X32
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != X32
        | r2_relset_1(X29,X30,X31,X32)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

fof(c_0_46,plain,(
    ! [X59,X60,X61] :
      ( ( k5_relat_1(X61,k2_funct_1(X61)) = k6_partfun1(X59)
        | X60 = k1_xboole_0
        | k2_relset_1(X59,X60,X61) != X60
        | ~ v2_funct_1(X61)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( k5_relat_1(k2_funct_1(X61),X61) = k6_partfun1(X60)
        | X60 = k1_xboole_0
        | k2_relset_1(X59,X60,X61) != X60
        | ~ v2_funct_1(X61)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X60)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_47,plain,(
    ! [X56,X57,X58] :
      ( ( v1_funct_1(k2_funct_1(X58))
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(k2_funct_1(X58),X57,X56)
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
        | ~ v2_funct_1(X58)
        | k2_relset_1(X56,X57,X58) != X57
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X57)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_48,negated_conjecture,
    ( k2_relset_1(X1,X2,esk4_0) = X2
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X3,esk4_0),k6_relat_1(X2))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_52,plain,
    ( v2_funct_1(X1)
    | X2 = k1_xboole_0
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))
    | k2_relset_1(X3,X4,X5) != X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_45])).

fof(c_0_57,plain,(
    ! [X33] : m1_subset_1(k6_relat_1(X33),k1_zfmisc_1(k2_zfmisc_1(X33,X33))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_58,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,X1,esk4_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_49]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v1_funct_2(X2,esk2_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_53]),c_0_54]),c_0_33])])).

cnf(c_0_63,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = X1
    | ~ r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_66,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v2_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_67,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_35])).

fof(c_0_68,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | k2_relat_1(esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_49]),c_0_30]),c_0_25])])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_33]),c_0_54]),c_0_45]),c_0_61]),c_0_32])])).

cnf(c_0_71,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | ~ v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_45]),c_0_50]),c_0_30]),c_0_25])]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_61])])).

cnf(c_0_73,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(X1)
    | X2 = k1_xboole_0
    | k2_relset_1(X1,X2,esk4_0) != X2
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_25])).

fof(c_0_75,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_76,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_77,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | r1_tarski(k2_relat_1(k5_relat_1(X11,X12)),k2_relat_1(X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_79,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_80,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0)
    | k2_relat_1(esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_30]),c_0_49]),c_0_50])]),c_0_63])).

cnf(c_0_81,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_84,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_86,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_70])])).

fof(c_0_87,plain,(
    ! [X13] :
      ( k1_relat_1(k6_relat_1(X13)) = X13
      & k2_relat_1(k6_relat_1(X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = k1_relat_1(esk4_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_25]),c_0_82])])).

fof(c_0_89,plain,(
    ! [X9,X10] :
      ( ( ~ v5_relat_1(X10,X9)
        | r1_tarski(k2_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k2_relat_1(X10),X9)
        | v5_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_90,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_32])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_54]),c_0_53]),c_0_32]),c_0_33]),c_0_83])])).

fof(c_0_93,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk4_0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_85])).

cnf(c_0_96,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_79])])).

cnf(c_0_97,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_79])])).

cnf(c_0_99,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_100,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk3_0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_33]),c_0_83]),c_0_91])])).

cnf(c_0_104,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97]),c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ v5_relat_1(k2_funct_1(esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_95]),c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_85])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))),k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(X1)
    | X2 = k1_xboole_0
    | k2_relset_1(X1,X2,esk3_0) != X2
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_33]),c_0_83])])).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ v5_relat_1(k2_funct_1(esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_102]),c_0_103])).

cnf(c_0_112,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_92])).

fof(c_0_113,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ v2_funct_1(X18)
      | k2_relat_1(X19) != k1_relat_1(X18)
      | k5_relat_1(X19,X18) != k6_relat_1(k2_relat_1(X18))
      | X19 = k2_funct_1(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | ~ r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_116,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))) = k1_relat_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_108])).

cnf(c_0_117,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_32]),c_0_53]),c_0_54])]),c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_119,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115])])).

cnf(c_0_121,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117]),c_0_97]),c_0_117]),c_0_97]),c_0_118])])).

cnf(c_0_122,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_53])).

cnf(c_0_123,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | k5_relat_1(X1,esk4_0) != k6_relat_1(esk1_0)
    | k2_relat_1(X1) != esk2_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_70]),c_0_25]),c_0_79]),c_0_82])])).

cnf(c_0_124,negated_conjecture,
    ( X1 = k2_funct_1(esk3_0)
    | k5_relat_1(X1,esk3_0) != k6_relat_1(esk2_0)
    | k2_relat_1(X1) != esk1_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_121]),c_0_122]),c_0_33]),c_0_83]),c_0_91])])).

cnf(c_0_125,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_126,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_72]),c_0_122]),c_0_33]),c_0_91])])).

cnf(c_0_127,negated_conjecture,
    ( k5_relat_1(esk4_0,esk3_0) != k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_70]),c_0_25]),c_0_82])]),c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_126]),c_0_127]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:23 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.38/0.62  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 0.38/0.62  # and selection function SelectDivPreferIntoLits.
% 0.38/0.62  #
% 0.38/0.62  # Preprocessing time       : 0.047 s
% 0.38/0.62  # Presaturation interreduction done
% 0.38/0.62  
% 0.38/0.62  # Proof found!
% 0.38/0.62  # SZS status Theorem
% 0.38/0.62  # SZS output start CNFRefutation
% 0.38/0.62  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.38/0.62  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.38/0.62  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.38/0.62  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 0.38/0.62  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.38/0.62  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.38/0.62  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 0.38/0.62  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.38/0.62  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.38/0.62  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.38/0.62  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.38/0.62  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.38/0.62  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.38/0.62  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.38/0.62  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.38/0.62  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.38/0.62  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.38/0.62  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.38/0.62  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.62  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 0.38/0.62  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.38/0.62  fof(c_0_21, plain, ![X34, X35, X36, X37, X38, X39]:((v1_funct_1(k1_partfun1(X34,X35,X36,X37,X38,X39))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(m1_subset_1(k1_partfun1(X34,X35,X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(X34,X37)))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.38/0.62  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.38/0.62  fof(c_0_23, plain, ![X40, X41, X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_partfun1(X40,X41,X42,X43,X44,X45)=k5_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.38/0.62  cnf(c_0_24, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.62  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_26, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.62  fof(c_0_27, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|(~r2_relset_1(X48,X48,k1_partfun1(X48,X47,X47,X48,X50,X49),k6_partfun1(X48))|k2_relset_1(X47,X48,X49)=X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.38/0.62  fof(c_0_28, plain, ![X46]:k6_partfun1(X46)=k6_relat_1(X46), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.38/0.62  cnf(c_0_29, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.38/0.62  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_31, negated_conjecture, (k1_partfun1(X1,X2,X3,X4,X5,esk4_0)=k5_relat_1(X5,esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.38/0.62  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_34, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.62  cnf(c_0_35, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.62  fof(c_0_36, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.38/0.62  cnf(c_0_37, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.38/0.62  cnf(c_0_38, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.38/0.62  cnf(c_0_39, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.38/0.62  cnf(c_0_40, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.62  cnf(c_0_41, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  fof(c_0_42, plain, ![X51, X52, X53, X54, X55]:(((v2_funct_1(X54)|X53=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_1(X55)|X53=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((v2_funct_1(X54)|X52!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_1(X55)|X52!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.38/0.62  fof(c_0_43, plain, ![X29, X30, X31, X32]:((~r2_relset_1(X29,X30,X31,X32)|X31=X32|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&(X31!=X32|r2_relset_1(X29,X30,X31,X32)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.38/0.62  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_33])).
% 0.38/0.62  cnf(c_0_45, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 0.38/0.62  fof(c_0_46, plain, ![X59, X60, X61]:((k5_relat_1(X61,k2_funct_1(X61))=k6_partfun1(X59)|X60=k1_xboole_0|(k2_relset_1(X59,X60,X61)!=X60|~v2_funct_1(X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(k5_relat_1(k2_funct_1(X61),X61)=k6_partfun1(X60)|X60=k1_xboole_0|(k2_relset_1(X59,X60,X61)!=X60|~v2_funct_1(X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.38/0.62  fof(c_0_47, plain, ![X56, X57, X58]:(((v1_funct_1(k2_funct_1(X58))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(k2_funct_1(X58),X57,X56)|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.38/0.62  cnf(c_0_48, negated_conjecture, (k2_relset_1(X1,X2,esk4_0)=X2|~v1_funct_2(esk4_0,X1,X2)|~v1_funct_2(X3,X2,X1)|~r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X3,esk4_0),k6_relat_1(X2))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.38/0.62  cnf(c_0_49, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.38/0.62  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_51, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_41, c_0_35])).
% 0.38/0.62  cnf(c_0_52, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.62  cnf(c_0_53, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_54, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_55, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.38/0.62  cnf(c_0_56, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_45])).
% 0.38/0.62  fof(c_0_57, plain, ![X33]:m1_subset_1(k6_relat_1(X33),k1_zfmisc_1(k2_zfmisc_1(X33,X33))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.38/0.62  cnf(c_0_58, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.62  cnf(c_0_59, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.62  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0|~v1_funct_2(X1,esk1_0,esk2_0)|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,X1,esk4_0),k6_relat_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_30]), c_0_49]), c_0_50])])).
% 0.38/0.62  cnf(c_0_61, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_51, c_0_45])).
% 0.38/0.62  cnf(c_0_62, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(X2)|~v1_funct_2(X2,esk2_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~v1_funct_1(X2)|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_53]), c_0_54]), c_0_33])])).
% 0.38/0.62  cnf(c_0_63, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_64, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=X1|~r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.38/0.62  cnf(c_0_65, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.38/0.62  fof(c_0_66, plain, ![X14]:(v1_relat_1(k6_relat_1(X14))&v2_funct_1(k6_relat_1(X14))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.38/0.62  cnf(c_0_67, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_58, c_0_35])).
% 0.38/0.62  fof(c_0_68, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.38/0.62  cnf(c_0_69, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|k2_relat_1(esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_50]), c_0_49]), c_0_30]), c_0_25])])).
% 0.38/0.62  cnf(c_0_70, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_33]), c_0_54]), c_0_45]), c_0_61]), c_0_32])])).
% 0.38/0.62  cnf(c_0_71, negated_conjecture, (v2_funct_1(esk4_0)|~v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_45]), c_0_50]), c_0_30]), c_0_25])]), c_0_63])).
% 0.38/0.62  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_61])])).
% 0.38/0.62  cnf(c_0_73, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.38/0.62  cnf(c_0_74, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(X1)|X2=k1_xboole_0|k2_relset_1(X1,X2,esk4_0)!=X2|~v1_funct_2(esk4_0,X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_25])).
% 0.38/0.62  fof(c_0_75, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_relat_1(X17)=k2_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.38/0.62  cnf(c_0_76, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.38/0.62  fof(c_0_77, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|r1_tarski(k2_relat_1(k5_relat_1(X11,X12)),k2_relat_1(X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.38/0.62  cnf(c_0_78, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.38/0.62  cnf(c_0_79, negated_conjecture, (v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.38/0.62  cnf(c_0_80, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)|k2_relat_1(esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_30]), c_0_49]), c_0_50])]), c_0_63])).
% 0.38/0.62  cnf(c_0_81, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.38/0.62  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_30])).
% 0.38/0.62  cnf(c_0_83, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_84, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.38/0.62  cnf(c_0_85, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.38/0.62  cnf(c_0_86, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_70])])).
% 0.38/0.62  fof(c_0_87, plain, ![X13]:(k1_relat_1(k6_relat_1(X13))=X13&k2_relat_1(k6_relat_1(X13))=X13), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.38/0.62  cnf(c_0_88, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=k1_relat_1(esk4_0)|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_25]), c_0_82])])).
% 0.38/0.62  fof(c_0_89, plain, ![X9, X10]:((~v5_relat_1(X10,X9)|r1_tarski(k2_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k2_relat_1(X10),X9)|v5_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.38/0.62  fof(c_0_90, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.38/0.62  cnf(c_0_91, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_76, c_0_32])).
% 0.38/0.62  cnf(c_0_92, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_54]), c_0_53]), c_0_32]), c_0_33]), c_0_83])])).
% 0.38/0.62  fof(c_0_93, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.62  cnf(c_0_94, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(esk4_0,X1)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_82])).
% 0.38/0.62  cnf(c_0_95, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_85])).
% 0.38/0.62  cnf(c_0_96, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_79])])).
% 0.38/0.62  cnf(c_0_97, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.38/0.62  cnf(c_0_98, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_79])])).
% 0.38/0.62  cnf(c_0_99, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.38/0.62  cnf(c_0_100, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.38/0.62  cnf(c_0_101, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(esk3_0,X1)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_91])).
% 0.38/0.62  cnf(c_0_102, negated_conjecture, (v1_relat_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_92])).
% 0.38/0.62  cnf(c_0_103, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_33]), c_0_83]), c_0_91])])).
% 0.38/0.62  cnf(c_0_104, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.38/0.62  cnf(c_0_105, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_97]), c_0_98])).
% 0.38/0.62  cnf(c_0_106, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~v5_relat_1(k2_funct_1(esk4_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_95]), c_0_98])).
% 0.38/0.62  cnf(c_0_107, negated_conjecture, (v5_relat_1(k2_funct_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_100, c_0_85])).
% 0.38/0.62  cnf(c_0_108, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))),k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])).
% 0.38/0.62  cnf(c_0_109, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(X1)|X2=k1_xboole_0|k2_relset_1(X1,X2,esk3_0)!=X2|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_33]), c_0_83])])).
% 0.38/0.62  cnf(c_0_110, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_111, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),X1)|~v5_relat_1(k2_funct_1(esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_102]), c_0_103])).
% 0.38/0.62  cnf(c_0_112, negated_conjecture, (v5_relat_1(k2_funct_1(esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_100, c_0_92])).
% 0.38/0.62  fof(c_0_113, plain, ![X18, X19]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~v1_relat_1(X19)|~v1_funct_1(X19)|(~v2_funct_1(X18)|k2_relat_1(X19)!=k1_relat_1(X18)|k5_relat_1(X19,X18)!=k6_relat_1(k2_relat_1(X18))|X19=k2_funct_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.38/0.62  cnf(c_0_114, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|~r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.38/0.62  cnf(c_0_115, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.38/0.62  cnf(c_0_116, negated_conjecture, (k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0)))=k1_relat_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),k2_relat_1(k5_relat_1(esk3_0,k2_funct_1(esk3_0))))), inference(spm,[status(thm)],[c_0_104, c_0_108])).
% 0.38/0.62  cnf(c_0_117, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_32]), c_0_53]), c_0_54])]), c_0_110])).
% 0.38/0.62  cnf(c_0_118, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_111, c_0_112])).
% 0.38/0.62  cnf(c_0_119, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.38/0.62  cnf(c_0_120, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115])])).
% 0.38/0.62  cnf(c_0_121, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117]), c_0_97]), c_0_117]), c_0_97]), c_0_118])])).
% 0.38/0.62  cnf(c_0_122, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_53])).
% 0.38/0.62  cnf(c_0_123, negated_conjecture, (X1=k2_funct_1(esk4_0)|k5_relat_1(X1,esk4_0)!=k6_relat_1(esk1_0)|k2_relat_1(X1)!=esk2_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_70]), c_0_25]), c_0_79]), c_0_82])])).
% 0.38/0.62  cnf(c_0_124, negated_conjecture, (X1=k2_funct_1(esk3_0)|k5_relat_1(X1,esk3_0)!=k6_relat_1(esk2_0)|k2_relat_1(X1)!=esk1_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_121]), c_0_122]), c_0_33]), c_0_83]), c_0_91])])).
% 0.38/0.62  cnf(c_0_125, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_126, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_72]), c_0_122]), c_0_33]), c_0_91])])).
% 0.38/0.62  cnf(c_0_127, negated_conjecture, (k5_relat_1(esk4_0,esk3_0)!=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_70]), c_0_25]), c_0_82])]), c_0_125])).
% 0.38/0.62  cnf(c_0_128, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_126]), c_0_127]), ['proof']).
% 0.38/0.62  # SZS output end CNFRefutation
% 0.38/0.62  # Proof object total steps             : 129
% 0.38/0.62  # Proof object clause steps            : 88
% 0.38/0.62  # Proof object formula steps           : 41
% 0.38/0.62  # Proof object conjectures             : 70
% 0.38/0.62  # Proof object clause conjectures      : 67
% 0.38/0.62  # Proof object formula conjectures     : 3
% 0.38/0.62  # Proof object initial clauses used    : 31
% 0.38/0.62  # Proof object initial formulas used   : 20
% 0.38/0.62  # Proof object generating inferences   : 44
% 0.38/0.62  # Proof object simplifying inferences  : 98
% 0.38/0.62  # Training examples: 0 positive, 0 negative
% 0.38/0.62  # Parsed axioms                        : 21
% 0.38/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.62  # Initial clauses                      : 48
% 0.38/0.62  # Removed in clause preprocessing      : 1
% 0.38/0.62  # Initial clauses in saturation        : 47
% 0.38/0.62  # Processed clauses                    : 1604
% 0.38/0.62  # ...of these trivial                  : 32
% 0.38/0.62  # ...subsumed                          : 76
% 0.38/0.62  # ...remaining for further processing  : 1496
% 0.38/0.62  # Other redundant clauses eliminated   : 18
% 0.38/0.62  # Clauses deleted for lack of memory   : 0
% 0.38/0.62  # Backward-subsumed                    : 0
% 0.38/0.62  # Backward-rewritten                   : 370
% 0.38/0.62  # Generated clauses                    : 6201
% 0.38/0.62  # ...of the previous two non-trivial   : 6277
% 0.38/0.62  # Contextual simplify-reflections      : 0
% 0.38/0.62  # Paramodulations                      : 6182
% 0.38/0.62  # Factorizations                       : 0
% 0.38/0.62  # Equation resolutions                 : 19
% 0.38/0.62  # Propositional unsat checks           : 0
% 0.38/0.62  #    Propositional check models        : 0
% 0.38/0.62  #    Propositional check unsatisfiable : 0
% 0.38/0.62  #    Propositional clauses             : 0
% 0.38/0.62  #    Propositional clauses after purity: 0
% 0.38/0.62  #    Propositional unsat core size     : 0
% 0.38/0.62  #    Propositional preprocessing time  : 0.000
% 0.38/0.62  #    Propositional encoding time       : 0.000
% 0.38/0.62  #    Propositional solver time         : 0.000
% 0.38/0.62  #    Success case prop preproc time    : 0.000
% 0.38/0.62  #    Success case prop encoding time   : 0.000
% 0.38/0.62  #    Success case prop solver time     : 0.000
% 0.38/0.62  # Current number of processed clauses  : 1075
% 0.38/0.62  #    Positive orientable unit clauses  : 410
% 0.38/0.62  #    Positive unorientable unit clauses: 0
% 0.38/0.62  #    Negative unit clauses             : 5
% 0.38/0.62  #    Non-unit-clauses                  : 660
% 0.38/0.62  # Current number of unprocessed clauses: 4596
% 0.38/0.62  # ...number of literals in the above   : 18227
% 0.38/0.62  # Current number of archived formulas  : 0
% 0.38/0.62  # Current number of archived clauses   : 417
% 0.38/0.62  # Clause-clause subsumption calls (NU) : 53229
% 0.38/0.62  # Rec. Clause-clause subsumption calls : 30338
% 0.38/0.62  # Non-unit clause-clause subsumptions  : 76
% 0.38/0.62  # Unit Clause-clause subsumption calls : 9476
% 0.38/0.62  # Rewrite failures with RHS unbound    : 0
% 0.38/0.62  # BW rewrite match attempts            : 7225
% 0.38/0.62  # BW rewrite match successes           : 48
% 0.38/0.62  # Condensation attempts                : 0
% 0.38/0.62  # Condensation successes               : 0
% 0.38/0.62  # Termbank termtop insertions          : 281023
% 0.38/0.62  
% 0.38/0.62  # -------------------------------------------------
% 0.38/0.62  # User time                : 0.261 s
% 0.38/0.62  # System time              : 0.016 s
% 0.38/0.62  # Total time               : 0.277 s
% 0.38/0.62  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
