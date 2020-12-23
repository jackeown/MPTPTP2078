%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:08 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  121 (3129 expanded)
%              Number of clauses        :   78 (1096 expanded)
%              Number of leaves         :   21 ( 787 expanded)
%              Depth                    :   21
%              Number of atoms          :  410 (20906 expanded)
%              Number of equality atoms :  125 (6496 expanded)
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

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

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

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    ! [X54] : k6_partfun1(X54) = k6_relat_1(X54) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_24,plain,(
    ! [X47] :
      ( v1_partfun1(k6_partfun1(X47),X47)
      & m1_subset_1(k6_partfun1(X47),k1_zfmisc_1(k2_zfmisc_1(X47,X47))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ r2_relset_1(X37,X38,X39,X40)
        | X39 = X40
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != X40
        | r2_relset_1(X37,X38,X39,X40)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
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
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( v1_funct_1(k1_partfun1(X41,X42,X43,X44,X45,X46))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( m1_subset_1(k1_partfun1(X41,X42,X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X41,X44)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_33,plain,(
    ! [X64,X65,X66] :
      ( ( k5_relat_1(X66,k2_funct_1(X66)) = k6_partfun1(X64)
        | X65 = k1_xboole_0
        | k2_relset_1(X64,X65,X66) != X65
        | ~ v2_funct_1(X66)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( k5_relat_1(k2_funct_1(X66),X66) = k6_partfun1(X65)
        | X65 = k1_xboole_0
        | k2_relset_1(X64,X65,X66) != X65
        | ~ v2_funct_1(X66)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,X64,X65)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_34,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k1_partfun1(X48,X49,X50,X51,X52,X53) = k5_relat_1(X52,X53) ) ),
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

cnf(c_0_42,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_44,plain,(
    ! [X28] : v2_funct_1(k6_relat_1(X28)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

cnf(c_0_45,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_48,plain,(
    ! [X59,X60,X61,X62,X63] :
      ( ( v2_funct_1(X62)
        | X61 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))
        | k2_relset_1(X59,X60,X62) != X60
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v2_funct_1(X63)
        | X61 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))
        | k2_relset_1(X59,X60,X62) != X60
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v2_funct_1(X62)
        | X60 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))
        | k2_relset_1(X59,X60,X62) != X60
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v2_funct_1(X63)
        | X60 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))
        | k2_relset_1(X59,X60,X62) != X60
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_49,negated_conjecture,
    ( k6_relat_1(esk2_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_50,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_51,plain,(
    ! [X55,X56,X57,X58] :
      ( ~ v1_funct_1(X57)
      | ~ v1_funct_2(X57,X55,X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
      | ~ v1_funct_1(X58)
      | ~ v1_funct_2(X58,X56,X55)
      | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))
      | ~ r2_relset_1(X56,X56,k1_partfun1(X56,X55,X55,X56,X58,X57),k6_partfun1(X56))
      | k2_relset_1(X55,X56,X57) = X56 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

cnf(c_0_52,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k6_relat_1(esk2_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_46]),c_0_37])]),c_0_47])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_59,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_43])).

cnf(c_0_61,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k5_relat_1(esk4_0,esk5_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57]),c_0_46]),c_0_58]),c_0_38]),c_0_37]),c_0_40]),c_0_39])]),c_0_47])).

cnf(c_0_64,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_49]),c_0_49])).

fof(c_0_66,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0
    | ~ v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_39]),c_0_46]),c_0_37])]),c_0_47])).

fof(c_0_68,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | k5_relat_1(k5_relat_1(X18,X19),X20) = k5_relat_1(X18,k5_relat_1(X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_69,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k5_relat_1(esk4_0,esk5_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_70,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_55]),c_0_57]),c_0_46]),c_0_49]),c_0_65]),c_0_38]),c_0_37]),c_0_40]),c_0_39])])).

cnf(c_0_71,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0)
    | k2_relset_1(esk3_0,esk2_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_63])])).

cnf(c_0_73,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_39])).

fof(c_0_76,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k5_relat_1(k6_relat_1(k1_relat_1(X22)),X22) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

fof(c_0_77,plain,(
    ! [X21] :
      ( k1_relat_1(k6_relat_1(X21)) = X21
      & k2_relat_1(k6_relat_1(X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_78,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_70])])).

cnf(c_0_79,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),k5_relat_1(esk5_0,X1)) = k5_relat_1(k5_relat_1(esk4_0,esk5_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_80,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_31])).

fof(c_0_83,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_84,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(k2_funct_1(esk5_0),X1)) = k5_relat_1(k6_relat_1(esk3_0),X1)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_75])])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0)) = k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_86,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])])).

fof(c_0_87,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ r1_tarski(k2_relat_1(X24),X23)
      | k5_relat_1(X24,k6_relat_1(X23)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_88,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0))) = k6_relat_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_40])).

cnf(c_0_91,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_88]),c_0_40])])).

fof(c_0_93,plain,(
    ! [X12] : m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_94,plain,(
    ! [X11] : k2_subset_1(X11) = X11 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_95,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(esk4_0,k6_relat_1(esk3_0))) = k6_relat_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_73]),c_0_78]),c_0_75]),c_0_90])])).

cnf(c_0_96,negated_conjecture,
    ( k5_relat_1(esk4_0,k6_relat_1(X1)) = esk4_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_90])])).

fof(c_0_97,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_98,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_99,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

fof(c_0_100,plain,(
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

fof(c_0_101,plain,(
    ! [X25] :
      ( ( v1_relat_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_102,negated_conjecture,
    ( k6_relat_1(esk3_0) = k5_relat_1(esk5_0,esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_70]),c_0_39])])).

cnf(c_0_106,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_107,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( k6_relat_1(esk3_0) = k5_relat_1(esk5_0,esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])])).

cnf(c_0_109,negated_conjecture,
    ( k5_relat_1(esk5_0,k6_relat_1(X1)) = esk5_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_105]),c_0_75])])).

cnf(c_0_110,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1)) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_106]),c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( k6_relat_1(esk3_0) = k5_relat_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_107]),c_0_37]),c_0_75])])).

cnf(c_0_112,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_113,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_114,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0)) = esk5_0
    | ~ r1_tarski(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_49])).

cnf(c_0_115,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk5_0,esk4_0),k2_funct_1(esk4_0)) = k2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_92]),c_0_111]),c_0_112]),c_0_38]),c_0_90])])).

cnf(c_0_116,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_56]),c_0_57]),c_0_112]),c_0_38])]),c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_103]),c_0_104])])).

cnf(c_0_118,negated_conjecture,
    ( esk5_0 != k2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_115]),c_0_116]),c_0_49]),c_0_117]),c_0_90]),c_0_75])]),c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_107]),c_0_38]),c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.033 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 0.13/0.40  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.13/0.40  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.13/0.40  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.40  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.13/0.40  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.13/0.40  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.13/0.40  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 0.13/0.40  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 0.13/0.40  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 0.13/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.40  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.13/0.40  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.13/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.40  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.13/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.40  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.13/0.40  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0&r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)))&v2_funct_1(esk4_0))&((esk2_0!=k1_xboole_0&esk3_0!=k1_xboole_0)&esk5_0!=k2_funct_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.13/0.40  fof(c_0_23, plain, ![X54]:k6_partfun1(X54)=k6_relat_1(X54), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.13/0.40  fof(c_0_24, plain, ![X47]:(v1_partfun1(k6_partfun1(X47),X47)&m1_subset_1(k6_partfun1(X47),k1_zfmisc_1(k2_zfmisc_1(X47,X47)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.13/0.40  fof(c_0_25, plain, ![X37, X38, X39, X40]:((~r2_relset_1(X37,X38,X39,X40)|X39=X40|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(X39!=X40|r2_relset_1(X37,X38,X39,X40)|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.40  cnf(c_0_26, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_27, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_28, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_29, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.40  cnf(c_0_31, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.13/0.40  fof(c_0_32, plain, ![X41, X42, X43, X44, X45, X46]:((v1_funct_1(k1_partfun1(X41,X42,X43,X44,X45,X46))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(m1_subset_1(k1_partfun1(X41,X42,X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X41,X44)))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.13/0.40  fof(c_0_33, plain, ![X64, X65, X66]:((k5_relat_1(X66,k2_funct_1(X66))=k6_partfun1(X64)|X65=k1_xboole_0|(k2_relset_1(X64,X65,X66)!=X65|~v2_funct_1(X66))|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&(k5_relat_1(k2_funct_1(X66),X66)=k6_partfun1(X65)|X65=k1_xboole_0|(k2_relset_1(X64,X65,X66)!=X65|~v2_funct_1(X66))|(~v1_funct_1(X66)|~v1_funct_2(X66,X64,X65)|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.13/0.40  fof(c_0_34, plain, ![X48, X49, X50, X51, X52, X53]:(~v1_funct_1(X52)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|k1_partfun1(X48,X49,X50,X51,X52,X53)=k5_relat_1(X52,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.13/0.40  cnf(c_0_36, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_41, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_42, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.13/0.40  fof(c_0_44, plain, ![X28]:v2_funct_1(k6_relat_1(X28)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.13/0.40  cnf(c_0_45, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_27])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  fof(c_0_48, plain, ![X59, X60, X61, X62, X63]:(((v2_funct_1(X62)|X61=k1_xboole_0|(~v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))|k2_relset_1(X59,X60,X62)!=X60)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(v2_funct_1(X63)|X61=k1_xboole_0|(~v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))|k2_relset_1(X59,X60,X62)!=X60)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))&((v2_funct_1(X62)|X60!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))|k2_relset_1(X59,X60,X62)!=X60)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(v2_funct_1(X63)|X60!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X59,X60,X60,X61,X62,X63))|k2_relset_1(X59,X60,X62)!=X60)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (k6_relat_1(esk2_0)=k5_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37]), c_0_38]), c_0_39]), c_0_40])])).
% 0.13/0.40  cnf(c_0_50, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  fof(c_0_51, plain, ![X55, X56, X57, X58]:(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))|(~v1_funct_1(X58)|~v1_funct_2(X58,X56,X55)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))|(~r2_relset_1(X56,X56,k1_partfun1(X56,X55,X55,X56,X58,X57),k6_partfun1(X56))|k2_relset_1(X55,X56,X57)=X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.13/0.40  cnf(c_0_52, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k6_relat_1(esk2_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_46]), c_0_37])]), c_0_47])).
% 0.13/0.40  cnf(c_0_54, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_43, c_0_49])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (v2_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.13/0.40  cnf(c_0_59, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k6_relat_1(esk2_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_30, c_0_43])).
% 0.13/0.40  cnf(c_0_61, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_52, c_0_27])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k5_relat_1(esk4_0,esk5_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(rw,[status(thm)],[c_0_53, c_0_49])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57]), c_0_46]), c_0_58]), c_0_38]), c_0_37]), c_0_40]), c_0_39])]), c_0_47])).
% 0.13/0.40  cnf(c_0_64, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_59, c_0_27])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k5_relat_1(esk4_0,esk5_0),k5_relat_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_49]), c_0_49])).
% 0.13/0.40  fof(c_0_66, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0|~v2_funct_1(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_39]), c_0_46]), c_0_37])]), c_0_47])).
% 0.13/0.40  fof(c_0_68, plain, ![X18, X19, X20]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~v1_relat_1(X20)|k5_relat_1(k5_relat_1(X18,X19),X20)=k5_relat_1(X18,k5_relat_1(X19,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k5_relat_1(esk4_0,esk5_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_55]), c_0_57]), c_0_46]), c_0_49]), c_0_65]), c_0_38]), c_0_37]), c_0_40]), c_0_39])])).
% 0.13/0.40  cnf(c_0_71, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)|k2_relset_1(esk3_0,esk2_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_63])])).
% 0.13/0.40  cnf(c_0_73, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_39])).
% 0.13/0.40  fof(c_0_76, plain, ![X22]:(~v1_relat_1(X22)|k5_relat_1(k6_relat_1(k1_relat_1(X22)),X22)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.13/0.40  fof(c_0_77, plain, ![X21]:(k1_relat_1(k6_relat_1(X21))=X21&k2_relat_1(k6_relat_1(X21))=X21), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_70])])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),k5_relat_1(esk5_0,X1))=k5_relat_1(k5_relat_1(esk4_0,esk5_0),X1)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.13/0.40  cnf(c_0_80, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.40  cnf(c_0_81, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.13/0.40  cnf(c_0_82, plain, (v1_relat_1(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_31])).
% 0.13/0.40  fof(c_0_83, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(k2_funct_1(esk5_0),X1))=k5_relat_1(k6_relat_1(esk3_0),X1)|~v1_relat_1(k2_funct_1(esk5_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_78]), c_0_75])])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),k6_relat_1(esk3_0))=k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_79, c_0_78])).
% 0.13/0.40  cnf(c_0_86, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])])).
% 0.13/0.40  fof(c_0_87, plain, ![X23, X24]:(~v1_relat_1(X24)|(~r1_tarski(k2_relat_1(X24),X23)|k5_relat_1(X24,k6_relat_1(X23))=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.13/0.40  cnf(c_0_88, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.13/0.40  cnf(c_0_89, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(k5_relat_1(esk4_0,esk5_0),k2_funct_1(esk5_0)))=k6_relat_1(esk3_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_82])])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_40])).
% 0.13/0.40  cnf(c_0_91, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.13/0.40  cnf(c_0_92, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_88]), c_0_40])])).
% 0.13/0.40  fof(c_0_93, plain, ![X12]:m1_subset_1(k2_subset_1(X12),k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.40  fof(c_0_94, plain, ![X11]:k2_subset_1(X11)=X11, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(esk4_0,k6_relat_1(esk3_0)))=k6_relat_1(esk3_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_73]), c_0_78]), c_0_75]), c_0_90])])).
% 0.13/0.40  cnf(c_0_96, negated_conjecture, (k5_relat_1(esk4_0,k6_relat_1(X1))=esk4_0|~r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_90])])).
% 0.13/0.40  fof(c_0_97, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  cnf(c_0_98, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.13/0.40  cnf(c_0_99, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.13/0.40  fof(c_0_100, plain, ![X29]:((k2_relat_1(X29)=k1_relat_1(k2_funct_1(X29))|~v2_funct_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(k1_relat_1(X29)=k2_relat_1(k2_funct_1(X29))|~v2_funct_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.40  fof(c_0_101, plain, ![X25]:((v1_relat_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(v1_funct_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.40  cnf(c_0_102, negated_conjecture, (k6_relat_1(esk3_0)=k5_relat_1(esk5_0,esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))|~r1_tarski(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.13/0.40  cnf(c_0_103, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.13/0.40  cnf(c_0_104, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.13/0.40  cnf(c_0_105, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_70]), c_0_39])])).
% 0.13/0.40  cnf(c_0_106, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.13/0.40  cnf(c_0_107, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.13/0.40  cnf(c_0_108, negated_conjecture, (k6_relat_1(esk3_0)=k5_relat_1(esk5_0,esk4_0)|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])])).
% 0.13/0.40  cnf(c_0_109, negated_conjecture, (k5_relat_1(esk5_0,k6_relat_1(X1))=esk5_0|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_105]), c_0_75])])).
% 0.13/0.40  cnf(c_0_110, plain, (k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_106]), c_0_107])).
% 0.13/0.40  cnf(c_0_111, negated_conjecture, (k6_relat_1(esk3_0)=k5_relat_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_107]), c_0_37]), c_0_75])])).
% 0.13/0.40  cnf(c_0_112, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_113, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_114, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0))=esk5_0|~r1_tarski(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_109, c_0_49])).
% 0.13/0.40  cnf(c_0_115, negated_conjecture, (k5_relat_1(k5_relat_1(esk5_0,esk4_0),k2_funct_1(esk4_0))=k2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_92]), c_0_111]), c_0_112]), c_0_38]), c_0_90])])).
% 0.13/0.40  cnf(c_0_116, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_40]), c_0_56]), c_0_57]), c_0_112]), c_0_38])]), c_0_113])).
% 0.13/0.40  cnf(c_0_117, negated_conjecture, (k5_relat_1(esk5_0,k5_relat_1(esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_103]), c_0_104])])).
% 0.13/0.40  cnf(c_0_118, negated_conjecture, (esk5_0!=k2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_119, negated_conjecture, (~v1_relat_1(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_115]), c_0_116]), c_0_49]), c_0_117]), c_0_90]), c_0_75])]), c_0_118])).
% 0.13/0.40  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_107]), c_0_38]), c_0_90])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 121
% 0.13/0.40  # Proof object clause steps            : 78
% 0.13/0.40  # Proof object formula steps           : 43
% 0.13/0.40  # Proof object conjectures             : 52
% 0.13/0.40  # Proof object clause conjectures      : 49
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 33
% 0.13/0.40  # Proof object initial formulas used   : 21
% 0.13/0.40  # Proof object generating inferences   : 31
% 0.13/0.40  # Proof object simplifying inferences  : 108
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 29
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 52
% 0.13/0.40  # Removed in clause preprocessing      : 2
% 0.13/0.40  # Initial clauses in saturation        : 50
% 0.13/0.40  # Processed clauses                    : 343
% 0.13/0.40  # ...of these trivial                  : 11
% 0.13/0.40  # ...subsumed                          : 48
% 0.13/0.40  # ...remaining for further processing  : 284
% 0.13/0.40  # Other redundant clauses eliminated   : 3
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 12
% 0.13/0.40  # Backward-rewritten                   : 72
% 0.13/0.40  # Generated clauses                    : 691
% 0.13/0.40  # ...of the previous two non-trivial   : 625
% 0.13/0.40  # Contextual simplify-reflections      : 3
% 0.13/0.40  # Paramodulations                      : 688
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 3
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 147
% 0.13/0.40  #    Positive orientable unit clauses  : 67
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 76
% 0.13/0.40  # Current number of unprocessed clauses: 371
% 0.13/0.40  # ...number of literals in the above   : 1526
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 136
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2258
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 863
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 59
% 0.13/0.40  # Unit Clause-clause subsumption calls : 400
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 21
% 0.13/0.40  # BW rewrite match successes           : 18
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 19007
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.059 s
% 0.13/0.41  # System time              : 0.007 s
% 0.13/0.41  # Total time               : 0.066 s
% 0.13/0.41  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
