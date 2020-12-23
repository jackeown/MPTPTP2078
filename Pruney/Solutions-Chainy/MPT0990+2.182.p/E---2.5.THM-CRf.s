%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 (13688 expanded)
%              Number of clauses        :   77 (4775 expanded)
%              Number of leaves         :   21 (3452 expanded)
%              Depth                    :   17
%              Number of atoms          :  450 (92444 expanded)
%              Number of equality atoms :  136 (28642 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

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

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

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

fof(t58_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))
    & v2_funct_1(esk4_0)
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & esk5_0 != k2_funct_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_23,plain,(
    ! [X55] : k6_partfun1(X55) = k6_relat_1(X55) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_24,plain,(
    ! [X48] :
      ( v1_partfun1(k6_partfun1(X48),X48)
      & m1_subset_1(k6_partfun1(X48),k1_zfmisc_1(k2_zfmisc_1(X48,X48))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X38,X39,X40,X41] :
      ( ( ~ r2_relset_1(X38,X39,X40,X41)
        | X40 = X41
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != X41
        | r2_relset_1(X38,X39,X40,X41)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_32,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_33,plain,(
    ! [X65,X66,X67] :
      ( ( k5_relat_1(X67,k2_funct_1(X67)) = k6_partfun1(X65)
        | X66 = k1_xboole_0
        | k2_relset_1(X65,X66,X67) != X66
        | ~ v2_funct_1(X67)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X65,X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
      & ( k5_relat_1(k2_funct_1(X67),X67) = k6_partfun1(X66)
        | X66 = k1_xboole_0
        | k2_relset_1(X65,X66,X67) != X66
        | ~ v2_funct_1(X67)
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,X65,X66)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_34,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ v1_funct_1(X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_partfun1(X49,X50,X51,X52,X53,X54) = k5_relat_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_35,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_43,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_44,plain,(
    ! [X56,X57,X58,X59] :
      ( ~ v1_funct_1(X58)
      | ~ v1_funct_2(X58,X56,X57)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X59)
      | ~ v1_funct_2(X59,X57,X56)
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
      | ~ r2_relset_1(X57,X57,k1_partfun1(X57,X56,X56,X57,X59,X58),k6_partfun1(X57))
      | k2_relset_1(X56,X57,X58) = X57 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

cnf(c_0_45,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_47,plain,(
    ! [X25] :
      ( v1_relat_1(k6_relat_1(X25))
      & v2_funct_1(k6_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_48,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_49,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k5_relat_1(k5_relat_1(X17,X18),X19) = k5_relat_1(X17,k5_relat_1(X18,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_50,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( k6_relat_1(esk2_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_57,plain,(
    ! [X60,X61,X62,X63,X64] :
      ( ( v2_funct_1(X63)
        | X62 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))
        | k2_relset_1(X60,X61,X63) != X61
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X61,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( v2_funct_1(X64)
        | X62 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))
        | k2_relset_1(X60,X61,X63) != X61
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X61,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( v2_funct_1(X63)
        | X61 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))
        | k2_relset_1(X60,X61,X63) != X61
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X61,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( v2_funct_1(X64)
        | X61 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))
        | k2_relset_1(X60,X61,X63) != X61
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X61,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_58,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_59,plain,(
    ! [X30] :
      ( ( k1_relat_1(k5_relat_1(X30,k2_funct_1(X30))) = k1_relat_1(X30)
        | ~ v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( k2_relat_1(k5_relat_1(X30,k2_funct_1(X30))) = k1_relat_1(X30)
        | ~ v2_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).

cnf(c_0_60,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_27])).

fof(c_0_61,plain,(
    ! [X20] :
      ( k1_relat_1(k6_relat_1(X20)) = X20
      & k2_relat_1(k6_relat_1(X20)) = X20 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_62,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k6_relat_1(esk2_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_51]),c_0_37])]),c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_39]),c_0_54])])).

cnf(c_0_65,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_68,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

fof(c_0_72,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_relset_1(X35,X36,X37) = k2_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_73,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_39]),c_0_51]),c_0_37])]),c_0_52])).

cnf(c_0_75,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),k5_relat_1(esk5_0,X1)) = k5_relat_1(k6_relat_1(esk2_0),X1)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_77,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0
    | ~ r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_51]),c_0_56]),c_0_38]),c_0_37]),c_0_40]),c_0_39])])).

cnf(c_0_78,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_56])).

cnf(c_0_80,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_66]),c_0_70]),c_0_67]),c_0_51]),c_0_71]),c_0_38]),c_0_37]),c_0_40]),c_0_39])]),c_0_52])).

fof(c_0_81,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k5_relat_1(X22,k6_relat_1(k2_relat_1(X22))) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_82,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_83,plain,(
    ! [X29] :
      ( ( k2_relat_1(X29) = k1_relat_1(k2_funct_1(X29))
        | ~ v2_funct_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_relat_1(X29) = k2_relat_1(k2_funct_1(X29))
        | ~ v2_funct_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_84,plain,(
    ! [X23] :
      ( ( v1_relat_1(k2_funct_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( v1_funct_1(k2_funct_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_37]),c_0_64])])).

cnf(c_0_86,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),k2_funct_1(esk5_0)) = k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_88,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_80])])).

cnf(c_0_89,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_82]),c_0_40])])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_40]),c_0_54])])).

cnf(c_0_92,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_80])])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0)) = k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_56]),c_0_87]),c_0_80])])).

cnf(c_0_96,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_87])])).

cnf(c_0_97,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(esk3_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_98,plain,
    ( k5_relat_1(k2_funct_1(X1),k6_relat_1(k1_relat_1(X1))) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_92]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_87])])).

fof(c_0_100,plain,(
    ! [X31] :
      ( ( k5_relat_1(X31,k2_funct_1(X31)) = k6_relat_1(k1_relat_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k5_relat_1(k2_funct_1(X31),X31) = k6_relat_1(k2_relat_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_101,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0)) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_95]),c_0_96]),c_0_97]),c_0_64]),c_0_91])])).

cnf(c_0_102,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0)) = k2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_80]),c_0_37]),c_0_64])])).

cnf(c_0_103,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(k2_funct_1(esk5_0),X1)) = k5_relat_1(k6_relat_1(esk3_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_96]),c_0_64])])).

cnf(c_0_104,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_87]),c_0_39])])).

cnf(c_0_106,negated_conjecture,
    ( k2_funct_1(esk5_0) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

fof(c_0_107,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k5_relat_1(k6_relat_1(k1_relat_1(X21)),X21) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_108,negated_conjecture,
    ( k5_relat_1(esk5_0,k6_relat_1(k1_relat_1(k2_funct_1(esk5_0)))) = k5_relat_1(k6_relat_1(esk3_0),k2_funct_1(k2_funct_1(esk5_0)))
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_93])).

cnf(c_0_109,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_110,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_105]),c_0_56]),c_0_64])])).

cnf(c_0_111,negated_conjecture,
    ( k2_funct_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_93]),c_0_37]),c_0_64])])).

cnf(c_0_112,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),k2_funct_1(k2_funct_1(esk5_0))) = esk5_0
    | ~ v2_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_105]),c_0_56]),c_0_110]),c_0_80]),c_0_37]),c_0_64])])).

cnf(c_0_114,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_115,negated_conjecture,
    ( k6_relat_1(esk3_0) = k5_relat_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_96,c_0_111])).

cnf(c_0_116,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1)) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_109]),c_0_93])).

cnf(c_0_117,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk5_0,esk4_0),k2_funct_1(esk4_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_111]),c_0_111]),c_0_114]),c_0_111]),c_0_38]),c_0_111]),c_0_91])]),c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( esk5_0 != k2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_90]),c_0_115]),c_0_117]),c_0_114]),c_0_38]),c_0_91])]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.030 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.20/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.42  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.42  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.42  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.20/0.42  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.20/0.42  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.42  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 0.20/0.42  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.42  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.20/0.42  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 0.20/0.42  fof(t58_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 0.20/0.42  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.42  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.20/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.42  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.20/0.42  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.20/0.42  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.20/0.42  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0&r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)))&v2_funct_1(esk4_0))&((esk2_0!=k1_xboole_0&esk3_0!=k1_xboole_0)&esk5_0!=k2_funct_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.42  fof(c_0_23, plain, ![X55]:k6_partfun1(X55)=k6_relat_1(X55), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.42  fof(c_0_24, plain, ![X48]:(v1_partfun1(k6_partfun1(X48),X48)&m1_subset_1(k6_partfun1(X48),k1_zfmisc_1(k2_zfmisc_1(X48,X48)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.42  fof(c_0_25, plain, ![X38, X39, X40, X41]:((~r2_relset_1(X38,X39,X40,X41)|X40=X41|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(X40!=X41|r2_relset_1(X38,X39,X40,X41)|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_27, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_28, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_29, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.42  cnf(c_0_31, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.20/0.42  fof(c_0_32, plain, ![X42, X43, X44, X45, X46, X47]:((v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.20/0.42  fof(c_0_33, plain, ![X65, X66, X67]:((k5_relat_1(X67,k2_funct_1(X67))=k6_partfun1(X65)|X66=k1_xboole_0|(k2_relset_1(X65,X66,X67)!=X66|~v2_funct_1(X67))|(~v1_funct_1(X67)|~v1_funct_2(X67,X65,X66)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))&(k5_relat_1(k2_funct_1(X67),X67)=k6_partfun1(X66)|X66=k1_xboole_0|(k2_relset_1(X65,X66,X67)!=X66|~v2_funct_1(X67))|(~v1_funct_1(X67)|~v1_funct_2(X67,X65,X66)|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.20/0.42  fof(c_0_34, plain, ![X49, X50, X51, X52, X53, X54]:(~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_partfun1(X49,X50,X51,X52,X53,X54)=k5_relat_1(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.42  cnf(c_0_36, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_41, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  fof(c_0_42, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.42  fof(c_0_43, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.42  fof(c_0_44, plain, ![X56, X57, X58, X59]:(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X57)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|(~v1_funct_1(X59)|~v1_funct_2(X59,X57,X56)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|(~r2_relset_1(X57,X57,k1_partfun1(X57,X56,X56,X57,X59,X58),k6_partfun1(X57))|k2_relset_1(X56,X57,X58)=X57))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.20/0.42  cnf(c_0_45, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.42  fof(c_0_47, plain, ![X25]:(v1_relat_1(k6_relat_1(X25))&v2_funct_1(k6_relat_1(X25))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.42  cnf(c_0_48, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  fof(c_0_49, plain, ![X17, X18, X19]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~v1_relat_1(X19)|k5_relat_1(k5_relat_1(X17,X18),X19)=k5_relat_1(X17,k5_relat_1(X18,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.20/0.42  cnf(c_0_50, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_27])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_53, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_55, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (k6_relat_1(esk2_0)=k5_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.42  fof(c_0_57, plain, ![X60, X61, X62, X63, X64]:(((v2_funct_1(X63)|X62=k1_xboole_0|(~v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))|k2_relset_1(X60,X61,X63)!=X61)|(~v1_funct_1(X64)|~v1_funct_2(X64,X61,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))))&(v2_funct_1(X64)|X62=k1_xboole_0|(~v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))|k2_relset_1(X60,X61,X63)!=X61)|(~v1_funct_1(X64)|~v1_funct_2(X64,X61,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))))&((v2_funct_1(X63)|X61!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))|k2_relset_1(X60,X61,X63)!=X61)|(~v1_funct_1(X64)|~v1_funct_2(X64,X61,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))))&(v2_funct_1(X64)|X61!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X60,X61,X61,X62,X63,X64))|k2_relset_1(X60,X61,X63)!=X61)|(~v1_funct_1(X64)|~v1_funct_2(X64,X61,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.20/0.42  cnf(c_0_58, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.42  fof(c_0_59, plain, ![X30]:((k1_relat_1(k5_relat_1(X30,k2_funct_1(X30)))=k1_relat_1(X30)|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(k2_relat_1(k5_relat_1(X30,k2_funct_1(X30)))=k1_relat_1(X30)|~v2_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).
% 0.20/0.42  cnf(c_0_60, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_48, c_0_27])).
% 0.20/0.42  fof(c_0_61, plain, ![X20]:(k1_relat_1(k6_relat_1(X20))=X20&k2_relat_1(k6_relat_1(X20))=X20), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.42  cnf(c_0_62, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k6_relat_1(esk2_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_39]), c_0_51]), c_0_37])]), c_0_52])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_39]), c_0_54])])).
% 0.20/0.42  cnf(c_0_65, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_55, c_0_27])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_46, c_0_56])).
% 0.20/0.42  cnf(c_0_67, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_68, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_69, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (v2_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.20/0.42  fof(c_0_72, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_relset_1(X35,X36,X37)=k2_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.42  cnf(c_0_73, plain, (k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_39]), c_0_51]), c_0_37])]), c_0_52])).
% 0.20/0.42  cnf(c_0_75, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),k5_relat_1(esk5_0,X1))=k5_relat_1(k6_relat_1(esk2_0),X1)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0|~r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_51]), c_0_56]), c_0_38]), c_0_37]), c_0_40]), c_0_39])])).
% 0.20/0.42  cnf(c_0_78, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_68])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_31, c_0_56])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_66]), c_0_70]), c_0_67]), c_0_51]), c_0_71]), c_0_38]), c_0_37]), c_0_40]), c_0_39])]), c_0_52])).
% 0.20/0.42  fof(c_0_81, plain, ![X22]:(~v1_relat_1(X22)|k5_relat_1(X22,k6_relat_1(k2_relat_1(X22)))=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.20/0.42  cnf(c_0_82, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.42  fof(c_0_83, plain, ![X29]:((k2_relat_1(X29)=k1_relat_1(k2_funct_1(X29))|~v2_funct_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(k1_relat_1(X29)=k2_relat_1(k2_funct_1(X29))|~v2_funct_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.42  fof(c_0_84, plain, ![X23]:((v1_relat_1(k2_funct_1(X23))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(v1_funct_1(k2_funct_1(X23))|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_37]), c_0_64])])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),k2_funct_1(esk5_0))=k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_76, c_0_74])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_80])])).
% 0.20/0.42  cnf(c_0_89, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_82]), c_0_40])])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_40]), c_0_54])])).
% 0.20/0.42  cnf(c_0_92, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.42  cnf(c_0_93, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_80])])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0))=k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_56]), c_0_87]), c_0_80])])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_87])])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(esk3_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 0.20/0.42  cnf(c_0_98, plain, (k5_relat_1(k2_funct_1(X1),k6_relat_1(k1_relat_1(X1)))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_92]), c_0_93])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_87])])).
% 0.20/0.42  fof(c_0_100, plain, ![X31]:((k5_relat_1(X31,k2_funct_1(X31))=k6_relat_1(k1_relat_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(k5_relat_1(k2_funct_1(X31),X31)=k6_relat_1(k2_relat_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))=esk4_0|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_95]), c_0_96]), c_0_97]), c_0_64]), c_0_91])])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))=k2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_80]), c_0_37]), c_0_64])])).
% 0.20/0.42  cnf(c_0_103, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(k2_funct_1(esk5_0),X1))=k5_relat_1(k6_relat_1(esk3_0),X1)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_96]), c_0_64])])).
% 0.20/0.42  cnf(c_0_104, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_87]), c_0_39])])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (k2_funct_1(esk5_0)=esk4_0|~v1_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.20/0.42  fof(c_0_107, plain, ![X21]:(~v1_relat_1(X21)|k5_relat_1(k6_relat_1(k1_relat_1(X21)),X21)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.20/0.42  cnf(c_0_108, negated_conjecture, (k5_relat_1(esk5_0,k6_relat_1(k1_relat_1(k2_funct_1(esk5_0))))=k5_relat_1(k6_relat_1(esk3_0),k2_funct_1(k2_funct_1(esk5_0)))|~v2_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_93])).
% 0.20/0.42  cnf(c_0_109, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.42  cnf(c_0_110, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_105]), c_0_56]), c_0_64])])).
% 0.20/0.42  cnf(c_0_111, negated_conjecture, (k2_funct_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_93]), c_0_37]), c_0_64])])).
% 0.20/0.42  cnf(c_0_112, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),k2_funct_1(k2_funct_1(esk5_0)))=esk5_0|~v2_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_105]), c_0_56]), c_0_110]), c_0_80]), c_0_37]), c_0_64])])).
% 0.20/0.42  cnf(c_0_114, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_115, negated_conjecture, (k6_relat_1(esk3_0)=k5_relat_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_96, c_0_111])).
% 0.20/0.42  cnf(c_0_116, plain, (k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_109]), c_0_93])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (k5_relat_1(k5_relat_1(esk5_0,esk4_0),k2_funct_1(esk4_0))=esk5_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_111]), c_0_111]), c_0_114]), c_0_111]), c_0_38]), c_0_111]), c_0_91])]), c_0_115])).
% 0.20/0.42  cnf(c_0_118, negated_conjecture, (esk5_0!=k2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_90]), c_0_115]), c_0_117]), c_0_114]), c_0_38]), c_0_91])]), c_0_118]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 120
% 0.20/0.42  # Proof object clause steps            : 77
% 0.20/0.42  # Proof object formula steps           : 43
% 0.20/0.42  # Proof object conjectures             : 50
% 0.20/0.42  # Proof object clause conjectures      : 47
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 34
% 0.20/0.42  # Proof object initial formulas used   : 21
% 0.20/0.42  # Proof object generating inferences   : 29
% 0.20/0.42  # Proof object simplifying inferences  : 119
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 33
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 62
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 60
% 0.20/0.42  # Processed clauses                    : 490
% 0.20/0.42  # ...of these trivial                  : 83
% 0.20/0.42  # ...subsumed                          : 75
% 0.20/0.42  # ...remaining for further processing  : 332
% 0.20/0.42  # Other redundant clauses eliminated   : 3
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 1
% 0.20/0.42  # Backward-rewritten                   : 109
% 0.20/0.42  # Generated clauses                    : 1109
% 0.20/0.42  # ...of the previous two non-trivial   : 891
% 0.20/0.42  # Contextual simplify-reflections      : 14
% 0.20/0.42  # Paramodulations                      : 1106
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 3
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 162
% 0.20/0.42  #    Positive orientable unit clauses  : 81
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 3
% 0.20/0.42  #    Non-unit-clauses                  : 78
% 0.20/0.42  # Current number of unprocessed clauses: 498
% 0.20/0.42  # ...number of literals in the above   : 2371
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 168
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3347
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1894
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 90
% 0.20/0.42  # Unit Clause-clause subsumption calls : 139
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 22
% 0.20/0.42  # BW rewrite match successes           : 19
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 30728
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.064 s
% 0.20/0.42  # System time              : 0.008 s
% 0.20/0.42  # Total time               : 0.072 s
% 0.20/0.42  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
