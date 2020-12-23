%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:12 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 937 expanded)
%              Number of clauses        :   78 ( 322 expanded)
%              Number of leaves         :   18 ( 230 expanded)
%              Depth                    :   13
%              Number of atoms          :  549 (7193 expanded)
%              Number of equality atoms :  136 (2357 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   40 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

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

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t59_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
          & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(t58_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(t63_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(fc7_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2)
        & v2_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v2_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t62_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X46] : k6_partfun1(X46) = k6_relat_1(X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0
    & r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))
    & v2_funct_1(esk5_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk6_0 != k2_funct_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
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

fof(c_0_23,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | ~ v1_funct_1(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_partfun1(X40,X41,X42,X43,X44,X45) = k5_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_24,plain,(
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

cnf(c_0_25,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_relset_1(X30,X31,X32,X33)
        | X32 = X33
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != X33
        | r2_relset_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_40,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k2_relset_1(X27,X28,X29) = k2_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_41,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_43,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_46,plain,(
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

cnf(c_0_47,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( k6_relat_1(esk3_0) = k5_relat_1(esk5_0,k2_funct_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_26])).

fof(c_0_52,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_53,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0) = k6_relat_1(esk3_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ m1_subset_1(k6_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(X1,esk3_0,X2) = esk3_0
    | ~ v1_funct_2(X3,esk3_0,X1)
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,X1,X1,esk3_0,X3,X2),k5_relat_1(esk5_0,k2_funct_1(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k5_relat_1(esk5_0,k2_funct_1(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_48])).

fof(c_0_60,plain,(
    ! [X19] :
      ( ( k1_relat_1(k5_relat_1(k2_funct_1(X19),X19)) = k2_relat_1(X19)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k2_relat_1(k5_relat_1(k2_funct_1(X19),X19)) = k2_relat_1(X19)
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_funct_1])])])).

cnf(c_0_61,negated_conjecture,
    ( k6_relat_1(esk4_0) = k5_relat_1(esk6_0,k2_funct_1(esk6_0))
    | k2_relset_1(esk4_0,esk3_0,esk6_0) != esk3_0
    | ~ v2_funct_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_44]),c_0_49]),c_0_45])]),c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( k6_relat_1(esk4_0) = k5_relat_1(k2_funct_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_63,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0) = k5_relat_1(esk5_0,k2_funct_1(esk5_0))
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_48]),c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k2_funct_1(X1),esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k2_relset_1(esk4_0,esk3_0,esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_35]),c_0_49]),c_0_33]),c_0_44]),c_0_37]),c_0_45])])).

cnf(c_0_68,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk6_0),esk6_0) = k5_relat_1(esk5_0,k2_funct_1(esk5_0))
    | k2_relset_1(esk4_0,esk3_0,esk6_0) != esk3_0
    | ~ v2_funct_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_48]),c_0_49]),c_0_45])]),c_0_50])).

fof(c_0_69,plain,(
    ! [X18] :
      ( ( k1_relat_1(k5_relat_1(X18,k2_funct_1(X18))) = k1_relat_1(X18)
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k2_relat_1(k5_relat_1(X18,k2_funct_1(X18))) = k1_relat_1(X18)
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).

cnf(c_0_70,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k5_relat_1(esk6_0,k2_funct_1(esk6_0))
    | k2_relset_1(esk4_0,esk3_0,esk6_0) != esk3_0
    | ~ v2_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_33])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = esk4_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_64]),c_0_33])])).

fof(c_0_74,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v2_funct_1(X22)
      | k2_relat_1(X22) != k1_relat_1(X23)
      | k5_relat_1(X22,X23) != k6_relat_1(k1_relat_1(X22))
      | X23 = k2_funct_1(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).

fof(c_0_75,plain,(
    ! [X20] :
      ( ( k5_relat_1(X20,k2_funct_1(X20)) = k6_relat_1(k1_relat_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k5_relat_1(k2_funct_1(X20),X20) = k6_relat_1(k2_relat_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_76,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k5_relat_1(esk5_0,esk6_0)
    | ~ m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ m1_subset_1(k5_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_30]),c_0_44]),c_0_33]),c_0_45]),c_0_37])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_33]),c_0_37])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_44]),c_0_67]),c_0_49]),c_0_45])])).

cnf(c_0_79,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk6_0),esk6_0) = k5_relat_1(esk5_0,k2_funct_1(esk5_0))
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_67])])).

cnf(c_0_80,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0))) = k2_relat_1(esk5_0)
    | k2_relset_1(esk4_0,esk3_0,esk6_0) != esk3_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_36]),c_0_37]),c_0_72])])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_44])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_73])).

cnf(c_0_84,plain,
    ( m1_subset_1(k5_relat_1(X1,k2_funct_1(X2)),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | k2_relset_1(X4,X5,X2) != X5
    | ~ v1_funct_2(X2,X4,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_56]),c_0_57])).

cnf(c_0_85,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k5_relat_1(esk5_0,esk6_0)
    | ~ m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | ~ v2_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk6_0) = k2_relat_1(esk5_0)
    | k2_relset_1(esk4_0,esk3_0,esk6_0) != esk3_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_45]),c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_33])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_33]),c_0_37])])).

cnf(c_0_92,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(X2,X1) != k5_relat_1(X2,k2_funct_1(X2))
    | k2_relat_1(X2) != k1_relat_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k5_relat_1(esk5_0,esk6_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | k2_relset_1(esk4_0,esk3_0,esk6_0) != esk3_0
    | ~ v2_funct_1(esk6_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_95,plain,(
    ! [X8,X9] :
      ( ( v1_relat_1(k5_relat_1(X8,X9))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) )
      & ( v2_funct_1(k5_relat_1(X8,X9))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).

fof(c_0_96,plain,(
    ! [X7] :
      ( ( v1_relat_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( v1_funct_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_97,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v2_funct_1(X21)
      | v2_funct_1(k2_funct_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).

fof(c_0_98,plain,(
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

cnf(c_0_99,negated_conjecture,
    ( k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0) = k5_relat_1(esk5_0,k2_funct_1(esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_29]),c_0_44]),c_0_33]),c_0_45]),c_0_37])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_101,negated_conjecture,
    ( X1 = k2_funct_1(esk5_0)
    | k5_relat_1(esk5_0,X1) != k5_relat_1(esk5_0,esk6_0)
    | k1_relat_1(X1) != esk4_0
    | ~ v2_funct_1(esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_90]),c_0_36]),c_0_37]),c_0_72])])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_67])])).

cnf(c_0_103,negated_conjecture,
    ( esk6_0 != k2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_104,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_105,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_106,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_107,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_108,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0) = k5_relat_1(esk5_0,k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_110,negated_conjecture,
    ( ~ v2_funct_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_45]),c_0_82])]),c_0_103])).

cnf(c_0_111,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_86]),c_0_105]),c_0_106]),c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( ~ v2_funct_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_34]),c_0_35]),c_0_49]),c_0_33]),c_0_44]),c_0_37]),c_0_45])]),c_0_50]),c_0_110])).

cnf(c_0_113,plain,
    ( v2_funct_1(k5_relat_1(X1,k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_111,c_0_86])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_36]),c_0_37]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 7.88/8.10  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.88/8.10  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.88/8.10  #
% 7.88/8.10  # Preprocessing time       : 0.030 s
% 7.88/8.10  # Presaturation interreduction done
% 7.88/8.10  
% 7.88/8.10  # Proof found!
% 7.88/8.10  # SZS status Theorem
% 7.88/8.10  # SZS output start CNFRefutation
% 7.88/8.10  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.88/8.10  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.88/8.10  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.88/8.10  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.88/8.10  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.88/8.10  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.88/8.10  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.88/8.10  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.88/8.10  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.88/8.10  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.88/8.10  fof(t59_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 7.88/8.10  fof(t58_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.88/8.10  fof(t63_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 7.88/8.10  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.88/8.10  fof(fc7_funct_1, axiom, ![X1, X2]:((((((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))&v2_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v2_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 7.88/8.10  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.88/8.10  fof(t62_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 7.88/8.10  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.88/8.10  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 7.88/8.10  fof(c_0_19, plain, ![X59, X60, X61]:((k5_relat_1(X61,k2_funct_1(X61))=k6_partfun1(X59)|X60=k1_xboole_0|(k2_relset_1(X59,X60,X61)!=X60|~v2_funct_1(X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(k5_relat_1(k2_funct_1(X61),X61)=k6_partfun1(X60)|X60=k1_xboole_0|(k2_relset_1(X59,X60,X61)!=X60|~v2_funct_1(X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X59,X60)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 7.88/8.10  fof(c_0_20, plain, ![X46]:k6_partfun1(X46)=k6_relat_1(X46), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 7.88/8.10  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0&r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0)))&v2_funct_1(esk5_0))&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk6_0!=k2_funct_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 7.88/8.10  fof(c_0_22, plain, ![X34, X35, X36, X37, X38, X39]:((v1_funct_1(k1_partfun1(X34,X35,X36,X37,X38,X39))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(m1_subset_1(k1_partfun1(X34,X35,X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(X34,X37)))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 7.88/8.10  fof(c_0_23, plain, ![X40, X41, X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_partfun1(X40,X41,X42,X43,X44,X45)=k5_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 7.88/8.10  fof(c_0_24, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|(~r2_relset_1(X48,X48,k1_partfun1(X48,X47,X47,X48,X50,X49),k6_partfun1(X48))|k2_relset_1(X47,X48,X49)=X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 7.88/8.10  cnf(c_0_25, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.88/8.10  cnf(c_0_26, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.88/8.10  fof(c_0_27, plain, ![X30, X31, X32, X33]:((~r2_relset_1(X30,X31,X32,X33)|X32=X33|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X32!=X33|r2_relset_1(X30,X31,X32,X33)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 7.88/8.10  cnf(c_0_28, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_29, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.88/8.10  cnf(c_0_30, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.88/8.10  cnf(c_0_31, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.88/8.10  cnf(c_0_32, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 7.88/8.10  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_34, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_36, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_38, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_39, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.88/8.10  fof(c_0_40, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k2_relset_1(X27,X28,X29)=k2_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 7.88/8.10  cnf(c_0_41, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.88/8.10  cnf(c_0_42, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_28, c_0_26])).
% 7.88/8.10  cnf(c_0_43, plain, (m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))|~v1_funct_1(X2)|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 7.88/8.10  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  fof(c_0_46, plain, ![X56, X57, X58]:(((v1_funct_1(k2_funct_1(X58))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(k2_funct_1(X58),X57,X56)|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(k2_funct_1(X58),k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|(~v2_funct_1(X58)|k2_relset_1(X56,X57,X58)!=X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 7.88/8.10  cnf(c_0_47, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_31, c_0_26])).
% 7.88/8.10  cnf(c_0_48, negated_conjecture, (k6_relat_1(esk3_0)=k5_relat_1(esk5_0,k2_funct_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 7.88/8.10  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_50, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_51, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_39, c_0_26])).
% 7.88/8.10  fof(c_0_52, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 7.88/8.10  cnf(c_0_53, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 7.88/8.10  cnf(c_0_54, negated_conjecture, (k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)=k6_relat_1(esk3_0)|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|~m1_subset_1(k6_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 7.88/8.10  cnf(c_0_55, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 7.88/8.10  cnf(c_0_56, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 7.88/8.10  cnf(c_0_57, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 7.88/8.10  cnf(c_0_58, negated_conjecture, (k2_relset_1(X1,esk3_0,X2)=esk3_0|~v1_funct_2(X3,esk3_0,X1)|~v1_funct_2(X2,X1,esk3_0)|~r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,X1,X1,esk3_0,X3,X2),k5_relat_1(esk5_0,k2_funct_1(esk5_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~v1_funct_1(X3)|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 7.88/8.10  cnf(c_0_59, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k5_relat_1(esk5_0,k2_funct_1(esk5_0)))), inference(rw,[status(thm)],[c_0_42, c_0_48])).
% 7.88/8.10  fof(c_0_60, plain, ![X19]:((k1_relat_1(k5_relat_1(k2_funct_1(X19),X19))=k2_relat_1(X19)|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k2_relat_1(k5_relat_1(k2_funct_1(X19),X19))=k2_relat_1(X19)|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_funct_1])])])).
% 7.88/8.10  cnf(c_0_61, negated_conjecture, (k6_relat_1(esk4_0)=k5_relat_1(esk6_0,k2_funct_1(esk6_0))|k2_relset_1(esk4_0,esk3_0,esk6_0)!=esk3_0|~v2_funct_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_44]), c_0_49]), c_0_45])]), c_0_50])).
% 7.88/8.10  cnf(c_0_62, negated_conjecture, (k6_relat_1(esk4_0)=k5_relat_1(k2_funct_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 7.88/8.10  cnf(c_0_63, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 7.88/8.10  cnf(c_0_64, plain, (k2_relset_1(X1,X2,X3)=k2_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_53, c_0_53])).
% 7.88/8.10  cnf(c_0_65, negated_conjecture, (k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)=k5_relat_1(esk5_0,k2_funct_1(esk5_0))|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|~m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_48]), c_0_48])).
% 7.88/8.10  cnf(c_0_66, negated_conjecture, (m1_subset_1(k5_relat_1(k2_funct_1(X1),esk6_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 7.88/8.10  cnf(c_0_67, negated_conjecture, (k2_relset_1(esk4_0,esk3_0,esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_35]), c_0_49]), c_0_33]), c_0_44]), c_0_37]), c_0_45])])).
% 7.88/8.10  cnf(c_0_68, negated_conjecture, (k5_relat_1(k2_funct_1(esk6_0),esk6_0)=k5_relat_1(esk5_0,k2_funct_1(esk5_0))|k2_relset_1(esk4_0,esk3_0,esk6_0)!=esk3_0|~v2_funct_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_48]), c_0_49]), c_0_45])]), c_0_50])).
% 7.88/8.10  fof(c_0_69, plain, ![X18]:((k1_relat_1(k5_relat_1(X18,k2_funct_1(X18)))=k1_relat_1(X18)|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k2_relat_1(k5_relat_1(X18,k2_funct_1(X18)))=k1_relat_1(X18)|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).
% 7.88/8.10  cnf(c_0_70, plain, (k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 7.88/8.10  cnf(c_0_71, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k5_relat_1(esk6_0,k2_funct_1(esk6_0))|k2_relset_1(esk4_0,esk3_0,esk6_0)!=esk3_0|~v2_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 7.88/8.10  cnf(c_0_72, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_33])).
% 7.88/8.10  cnf(c_0_73, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=esk4_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_64]), c_0_33])])).
% 7.88/8.10  fof(c_0_74, plain, ![X22, X23]:(~v1_relat_1(X22)|~v1_funct_1(X22)|(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v2_funct_1(X22)|k2_relat_1(X22)!=k1_relat_1(X23)|k5_relat_1(X22,X23)!=k6_relat_1(k1_relat_1(X22))|X23=k2_funct_1(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).
% 7.88/8.10  fof(c_0_75, plain, ![X20]:((k5_relat_1(X20,k2_funct_1(X20))=k6_relat_1(k1_relat_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(k5_relat_1(k2_funct_1(X20),X20)=k6_relat_1(k2_relat_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 7.88/8.10  cnf(c_0_76, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k5_relat_1(esk5_0,esk6_0)|~m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|~m1_subset_1(k5_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_30]), c_0_44]), c_0_33]), c_0_45]), c_0_37])])).
% 7.88/8.10  cnf(c_0_77, negated_conjecture, (m1_subset_1(k5_relat_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_33]), c_0_37])])).
% 7.88/8.10  cnf(c_0_78, negated_conjecture, (m1_subset_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_44]), c_0_67]), c_0_49]), c_0_45])])).
% 7.88/8.10  cnf(c_0_79, negated_conjecture, (k5_relat_1(k2_funct_1(esk6_0),esk6_0)=k5_relat_1(esk5_0,k2_funct_1(esk5_0))|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_67])])).
% 7.88/8.10  cnf(c_0_80, plain, (k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 7.88/8.10  cnf(c_0_81, negated_conjecture, (k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)))=k2_relat_1(esk5_0)|k2_relset_1(esk4_0,esk3_0,esk6_0)!=esk3_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_36]), c_0_37]), c_0_72])])).
% 7.88/8.10  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_44])).
% 7.88/8.10  cnf(c_0_83, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_73])).
% 7.88/8.10  cnf(c_0_84, plain, (m1_subset_1(k5_relat_1(X1,k2_funct_1(X2)),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|k2_relset_1(X4,X5,X2)!=X5|~v1_funct_2(X2,X4,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_56]), c_0_57])).
% 7.88/8.10  cnf(c_0_85, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 7.88/8.10  cnf(c_0_86, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 7.88/8.10  cnf(c_0_87, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k5_relat_1(esk5_0,esk6_0)|~m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 7.88/8.10  cnf(c_0_88, negated_conjecture, (m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|~v2_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 7.88/8.10  cnf(c_0_89, negated_conjecture, (k1_relat_1(esk6_0)=k2_relat_1(esk5_0)|k2_relset_1(esk4_0,esk3_0,esk6_0)!=esk3_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_45]), c_0_82])])).
% 7.88/8.10  cnf(c_0_90, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_83, c_0_33])).
% 7.88/8.10  cnf(c_0_91, negated_conjecture, (m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(X1)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_33]), c_0_37])])).
% 7.88/8.10  cnf(c_0_92, plain, (X1=k2_funct_1(X2)|k5_relat_1(X2,X1)!=k5_relat_1(X2,k2_funct_1(X2))|k2_relat_1(X2)!=k1_relat_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 7.88/8.10  cnf(c_0_93, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k5_relat_1(esk5_0,esk6_0)|~v2_funct_1(esk6_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 7.88/8.10  cnf(c_0_94, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|k2_relset_1(esk4_0,esk3_0,esk6_0)!=esk3_0|~v2_funct_1(esk6_0)), inference(rw,[status(thm)],[c_0_89, c_0_90])).
% 7.88/8.10  fof(c_0_95, plain, ![X8, X9]:((v1_relat_1(k5_relat_1(X8,X9))|(~v1_relat_1(X8)|~v1_funct_1(X8)|~v2_funct_1(X8)|~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9)))&(v2_funct_1(k5_relat_1(X8,X9))|(~v1_relat_1(X8)|~v1_funct_1(X8)|~v2_funct_1(X8)|~v1_relat_1(X9)|~v1_funct_1(X9)|~v2_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).
% 7.88/8.10  fof(c_0_96, plain, ![X7]:((v1_relat_1(k2_funct_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(v1_funct_1(k2_funct_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 7.88/8.10  fof(c_0_97, plain, ![X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~v2_funct_1(X21)|v2_funct_1(k2_funct_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).
% 7.88/8.10  fof(c_0_98, plain, ![X51, X52, X53, X54, X55]:(((v2_funct_1(X54)|X53=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_1(X55)|X53=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((v2_funct_1(X54)|X52!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(v2_funct_1(X55)|X52!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X51,X52,X52,X53,X54,X55))|k2_relset_1(X51,X52,X54)!=X52)|(~v1_funct_1(X55)|~v1_funct_2(X55,X52,X53)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 7.88/8.10  cnf(c_0_99, negated_conjecture, (k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)=k5_relat_1(esk5_0,k2_funct_1(esk5_0))|~m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_29]), c_0_44]), c_0_33]), c_0_45]), c_0_37])])).
% 7.88/8.10  cnf(c_0_100, negated_conjecture, (m1_subset_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 7.88/8.10  cnf(c_0_101, negated_conjecture, (X1=k2_funct_1(esk5_0)|k5_relat_1(esk5_0,X1)!=k5_relat_1(esk5_0,esk6_0)|k1_relat_1(X1)!=esk4_0|~v2_funct_1(esk6_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_90]), c_0_36]), c_0_37]), c_0_72])])).
% 7.88/8.10  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_67])])).
% 7.88/8.10  cnf(c_0_103, negated_conjecture, (esk6_0!=k2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.88/8.10  cnf(c_0_104, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 7.88/8.10  cnf(c_0_105, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 7.88/8.10  cnf(c_0_106, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 7.88/8.10  cnf(c_0_107, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 7.88/8.10  cnf(c_0_108, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 7.88/8.10  cnf(c_0_109, negated_conjecture, (k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)=k5_relat_1(esk5_0,k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 7.88/8.10  cnf(c_0_110, negated_conjecture, (~v2_funct_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_45]), c_0_82])]), c_0_103])).
% 7.88/8.10  cnf(c_0_111, plain, (v2_funct_1(k6_relat_1(k1_relat_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_86]), c_0_105]), c_0_106]), c_0_107])).
% 7.88/8.10  cnf(c_0_112, negated_conjecture, (~v2_funct_1(k5_relat_1(esk5_0,k2_funct_1(esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_34]), c_0_35]), c_0_49]), c_0_33]), c_0_44]), c_0_37]), c_0_45])]), c_0_50]), c_0_110])).
% 7.88/8.10  cnf(c_0_113, plain, (v2_funct_1(k5_relat_1(X1,k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_111, c_0_86])).
% 7.88/8.10  cnf(c_0_114, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_36]), c_0_37]), c_0_72])]), ['proof']).
% 7.88/8.10  # SZS output end CNFRefutation
% 7.88/8.10  # Proof object total steps             : 115
% 7.88/8.10  # Proof object clause steps            : 78
% 7.88/8.10  # Proof object formula steps           : 37
% 7.88/8.10  # Proof object conjectures             : 52
% 7.88/8.10  # Proof object clause conjectures      : 49
% 7.88/8.10  # Proof object formula conjectures     : 3
% 7.88/8.10  # Proof object initial clauses used    : 32
% 7.88/8.10  # Proof object initial formulas used   : 18
% 7.88/8.10  # Proof object generating inferences   : 35
% 7.88/8.10  # Proof object simplifying inferences  : 106
% 7.88/8.10  # Training examples: 0 positive, 0 negative
% 7.88/8.10  # Parsed axioms                        : 21
% 7.88/8.10  # Removed by relevancy pruning/SinE    : 0
% 7.88/8.10  # Initial clauses                      : 45
% 7.88/8.10  # Removed in clause preprocessing      : 1
% 7.88/8.10  # Initial clauses in saturation        : 44
% 7.88/8.10  # Processed clauses                    : 31145
% 7.88/8.10  # ...of these trivial                  : 216
% 7.88/8.10  # ...subsumed                          : 19308
% 7.88/8.10  # ...remaining for further processing  : 11621
% 7.88/8.10  # Other redundant clauses eliminated   : 482
% 7.88/8.10  # Clauses deleted for lack of memory   : 0
% 7.88/8.10  # Backward-subsumed                    : 1148
% 7.88/8.10  # Backward-rewritten                   : 613
% 7.88/8.10  # Generated clauses                    : 478467
% 7.88/8.10  # ...of the previous two non-trivial   : 470167
% 7.88/8.10  # Contextual simplify-reflections      : 900
% 7.88/8.10  # Paramodulations                      : 477984
% 7.88/8.10  # Factorizations                       : 0
% 7.88/8.10  # Equation resolutions                 : 483
% 7.88/8.10  # Propositional unsat checks           : 2
% 7.88/8.10  #    Propositional check models        : 1
% 7.88/8.10  #    Propositional check unsatisfiable : 0
% 7.88/8.10  #    Propositional clauses             : 0
% 7.88/8.10  #    Propositional clauses after purity: 0
% 7.88/8.10  #    Propositional unsat core size     : 0
% 7.88/8.10  #    Propositional preprocessing time  : 0.000
% 7.88/8.10  #    Propositional encoding time       : 0.240
% 7.88/8.10  #    Propositional solver time         : 0.065
% 7.88/8.10  #    Success case prop preproc time    : 0.000
% 7.88/8.10  #    Success case prop encoding time   : 0.000
% 7.88/8.10  #    Success case prop solver time     : 0.000
% 7.88/8.10  # Current number of processed clauses  : 9813
% 7.88/8.10  #    Positive orientable unit clauses  : 6058
% 7.88/8.10  #    Positive unorientable unit clauses: 0
% 7.88/8.10  #    Negative unit clauses             : 5
% 7.88/8.10  #    Non-unit-clauses                  : 3750
% 7.88/8.10  # Current number of unprocessed clauses: 437794
% 7.88/8.10  # ...number of literals in the above   : 1577019
% 7.88/8.10  # Current number of archived formulas  : 0
% 7.88/8.10  # Current number of archived clauses   : 1806
% 7.88/8.10  # Clause-clause subsumption calls (NU) : 1359360
% 7.88/8.10  # Rec. Clause-clause subsumption calls : 290089
% 7.88/8.10  # Non-unit clause-clause subsumptions  : 15201
% 7.88/8.10  # Unit Clause-clause subsumption calls : 480277
% 7.88/8.10  # Rewrite failures with RHS unbound    : 0
% 7.88/8.10  # BW rewrite match attempts            : 2451043
% 7.88/8.10  # BW rewrite match successes           : 33
% 7.88/8.10  # Condensation attempts                : 0
% 7.88/8.10  # Condensation successes               : 0
% 7.88/8.10  # Termbank termtop insertions          : 26352217
% 7.97/8.12  
% 7.97/8.12  # -------------------------------------------------
% 7.97/8.12  # User time                : 7.546 s
% 7.97/8.12  # System time              : 0.229 s
% 7.97/8.12  # Total time               : 7.775 s
% 7.97/8.12  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
