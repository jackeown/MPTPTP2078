%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:02 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  108 (1679 expanded)
%              Number of clauses        :   79 ( 627 expanded)
%              Number of leaves         :   14 ( 399 expanded)
%              Depth                    :   15
%              Number of atoms          :  417 (12039 expanded)
%              Number of equality atoms :  137 (3726 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( v1_funct_1(k1_partfun1(X25,X26,X27,X28,X29,X30))
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( m1_subset_1(k1_partfun1(X25,X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X25,X28)))
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_16,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X51,X52,X53] :
      ( ( k5_relat_1(X53,k2_funct_1(X53)) = k6_partfun1(X51)
        | X52 = k1_xboole_0
        | k2_relset_1(X51,X52,X53) != X52
        | ~ v2_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( k5_relat_1(k2_funct_1(X53),X53) = k6_partfun1(X52)
        | X52 = k1_xboole_0
        | k2_relset_1(X51,X52,X53) != X52
        | ~ v2_funct_1(X53)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_18,plain,(
    ! [X37] : k6_partfun1(X37) = k6_relat_1(X37) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X46,X47,X48,X49,X50] :
      ( ( v2_funct_1(X49)
        | X48 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))
        | k2_relset_1(X46,X47,X49) != X47
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X47,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v2_funct_1(X50)
        | X48 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))
        | k2_relset_1(X46,X47,X49) != X47
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X47,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v2_funct_1(X49)
        | X47 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))
        | k2_relset_1(X46,X47,X49) != X47
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X47,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v2_funct_1(X50)
        | X47 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))
        | k2_relset_1(X46,X47,X49) != X47
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X47,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X46,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X18,X19,X20,X21] :
      ( ( ~ r2_relset_1(X18,X19,X20,X21)
        | X20 = X21
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X20 != X21
        | r2_relset_1(X18,X19,X20,X21)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_39,plain,(
    ! [X22] : m1_subset_1(k6_relat_1(X22),k1_zfmisc_1(k2_zfmisc_1(X22,X22))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_41,plain,(
    ! [X7] :
      ( k1_relat_1(k6_relat_1(X7)) = X7
      & k2_relat_1(k6_relat_1(X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_42,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_29]),c_0_33]),c_0_34])]),c_0_35])).

fof(c_0_45,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ v1_funct_1(X36)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_partfun1(X31,X32,X33,X34,X35,X36) = k5_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v1_funct_2(X2,esk2_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_32]),c_0_31]),c_0_33])])).

cnf(c_0_47,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_49,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

fof(c_0_51,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v2_funct_1(X10)
      | k2_relat_1(X11) != k1_relat_1(X10)
      | k5_relat_1(X11,X10) != k6_relat_1(k2_relat_1(X10))
      | X11 = k2_funct_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).

cnf(c_0_52,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( k6_relat_1(k2_relat_1(esk3_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_33]),c_0_34])]),c_0_44])).

cnf(c_0_54,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk2_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

fof(c_0_60,plain,(
    ! [X8] :
      ( v1_relat_1(k6_relat_1(X8))
      & v2_funct_1(k6_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_61,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,X38,X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,X39,X38)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
      | ~ r2_relset_1(X39,X39,k1_partfun1(X39,X38,X38,X39,X41,X40),k6_partfun1(X39))
      | k2_relset_1(X38,X39,X40) = X39 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

cnf(c_0_62,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X2) != k1_relat_1(X1)
    | k5_relat_1(X2,X1) != k6_relat_1(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3) = k5_relat_1(esk3_0,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_26])]),c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_69,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( k2_funct_1(X1) = esk3_0
    | k6_relat_1(k2_relat_1(X1)) != k5_relat_1(esk3_0,X1)
    | k1_relat_1(X1) != esk2_0
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_33]),c_0_43])]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k6_relat_1(k2_relat_1(esk4_0))
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_66]),c_0_20])])).

cnf(c_0_76,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_77,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_23])).

cnf(c_0_78,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_79,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_80,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_32]),c_0_31]),c_0_29]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_81,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | k6_relat_1(k2_relat_1(esk4_0)) != k5_relat_1(esk3_0,esk4_0)
    | k1_relat_1(esk4_0) != esk2_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_20]),c_0_66])])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k6_relat_1(esk1_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_56]),c_0_26]),c_0_20])]),c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk4_0),esk4_0) = k6_relat_1(k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_85,negated_conjecture,
    ( k2_relset_1(X1,X2,X3) = X2
    | ~ v1_funct_2(esk3_0,X2,X1)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,esk3_0,X3),k6_relat_1(X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_33])).

cnf(c_0_86,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_49])).

cnf(c_0_87,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_34]),c_0_33]),c_0_43])]),c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | k6_relat_1(k2_relat_1(esk4_0)) != k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)
    | k1_relat_1(esk4_0) != esk2_0
    | ~ v2_funct_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( k6_relat_1(k2_relat_1(esk4_0)) = k6_relat_1(esk1_0)
    | k2_relset_1(esk2_0,esk1_0,esk4_0) != esk1_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_76])]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_26]),c_0_31]),c_0_56]),c_0_68]),c_0_86]),c_0_29]),c_0_20])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_76]),c_0_20]),c_0_66])])).

cnf(c_0_92,negated_conjecture,
    ( k2_funct_1(X1) = esk4_0
    | k6_relat_1(k2_relat_1(X1)) != k5_relat_1(esk4_0,X1)
    | k1_relat_1(X1) != k2_relat_1(esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_20]),c_0_66])])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_87]),c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_95,negated_conjecture,
    ( k1_partfun1(esk2_0,esk1_0,X1,X2,esk4_0,X3) = k5_relat_1(esk4_0,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_26]),c_0_20])])).

cnf(c_0_96,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | k6_relat_1(k2_relat_1(esk4_0)) != k6_relat_1(esk1_0)
    | k1_relat_1(esk4_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_68]),c_0_76])])).

cnf(c_0_97,negated_conjecture,
    ( k6_relat_1(k2_relat_1(esk4_0)) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_98,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_90]),c_0_91]),c_0_56]),c_0_26]),c_0_20]),c_0_76])]),c_0_57])).

cnf(c_0_99,negated_conjecture,
    ( k5_relat_1(esk4_0,esk3_0) != k6_relat_1(esk2_0)
    | k2_relat_1(esk4_0) != esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_64]),c_0_93]),c_0_33]),c_0_34]),c_0_43])]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( k5_relat_1(esk4_0,esk3_0) = k1_partfun1(esk2_0,esk1_0,esk1_0,esk2_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_29]),c_0_33])])).

cnf(c_0_101,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | k1_relat_1(esk4_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_98]),c_0_52])).

cnf(c_0_103,negated_conjecture,
    ( k1_partfun1(esk2_0,esk1_0,esk1_0,esk2_0,esk4_0,esk3_0) != k6_relat_1(esk2_0)
    | k2_relat_1(esk4_0) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_97]),c_0_52])).

cnf(c_0_105,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_106,negated_conjecture,
    ( k1_partfun1(esk2_0,esk1_0,esk1_0,esk2_0,esk4_0,esk3_0) != k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_98]),c_0_105]),c_0_100]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:16:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 0.18/0.44  # and selection function SelectDivPreferIntoLits.
% 0.18/0.44  #
% 0.18/0.44  # Preprocessing time       : 0.033 s
% 0.18/0.44  # Presaturation interreduction done
% 0.18/0.44  
% 0.18/0.44  # Proof found!
% 0.18/0.44  # SZS status Theorem
% 0.18/0.44  # SZS output start CNFRefutation
% 0.18/0.44  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.18/0.44  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.18/0.44  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.18/0.44  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.18/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.44  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 0.18/0.44  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.18/0.44  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.18/0.44  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.18/0.44  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.18/0.44  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.18/0.44  fof(t64_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 0.18/0.44  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.18/0.44  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 0.18/0.44  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.18/0.44  fof(c_0_15, plain, ![X25, X26, X27, X28, X29, X30]:((v1_funct_1(k1_partfun1(X25,X26,X27,X28,X29,X30))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&(m1_subset_1(k1_partfun1(X25,X26,X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X25,X28)))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.18/0.44  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.18/0.44  fof(c_0_17, plain, ![X51, X52, X53]:((k5_relat_1(X53,k2_funct_1(X53))=k6_partfun1(X51)|X52=k1_xboole_0|(k2_relset_1(X51,X52,X53)!=X52|~v2_funct_1(X53))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(k5_relat_1(k2_funct_1(X53),X53)=k6_partfun1(X52)|X52=k1_xboole_0|(k2_relset_1(X51,X52,X53)!=X52|~v2_funct_1(X53))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.18/0.44  fof(c_0_18, plain, ![X37]:k6_partfun1(X37)=k6_relat_1(X37), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.18/0.44  cnf(c_0_19, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.44  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  fof(c_0_21, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.44  cnf(c_0_22, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.44  cnf(c_0_23, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.44  fof(c_0_24, plain, ![X46, X47, X48, X49, X50]:(((v2_funct_1(X49)|X48=k1_xboole_0|(~v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))|k2_relset_1(X46,X47,X49)!=X47)|(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&(v2_funct_1(X50)|X48=k1_xboole_0|(~v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))|k2_relset_1(X46,X47,X49)!=X47)|(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&((v2_funct_1(X49)|X47!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))|k2_relset_1(X46,X47,X49)!=X47)|(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&(v2_funct_1(X50)|X47!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X46,X47,X47,X48,X49,X50))|k2_relset_1(X46,X47,X49)!=X47)|(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 0.18/0.44  cnf(c_0_25, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.44  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  fof(c_0_27, plain, ![X9]:((k5_relat_1(X9,k2_funct_1(X9))=k6_relat_1(k1_relat_1(X9))|~v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(k5_relat_1(k2_funct_1(X9),X9)=k6_relat_1(k2_relat_1(X9))|~v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.18/0.44  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.44  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_30, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.44  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_32, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_34, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_35, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_36, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.44  fof(c_0_37, plain, ![X18, X19, X20, X21]:((~r2_relset_1(X18,X19,X20,X21)|X20=X21|(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&(X20!=X21|r2_relset_1(X18,X19,X20,X21)|(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.18/0.44  cnf(c_0_38, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  fof(c_0_39, plain, ![X22]:m1_subset_1(k6_relat_1(X22),k1_zfmisc_1(k2_zfmisc_1(X22,X22))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.18/0.44  cnf(c_0_40, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.44  fof(c_0_41, plain, ![X7]:(k1_relat_1(k6_relat_1(X7))=X7&k2_relat_1(k6_relat_1(X7))=X7), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.18/0.44  cnf(c_0_42, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.44  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.44  cnf(c_0_44, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),esk3_0)=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_29]), c_0_33]), c_0_34])]), c_0_35])).
% 0.18/0.44  fof(c_0_45, plain, ![X31, X32, X33, X34, X35, X36]:(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_partfun1(X31,X32,X33,X34,X35,X36)=k5_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.18/0.44  cnf(c_0_46, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(X2)|~v1_funct_2(X2,esk2_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~v1_funct_1(X2)|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_32]), c_0_31]), c_0_33])])).
% 0.18/0.44  cnf(c_0_47, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.44  cnf(c_0_48, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_38, c_0_23])).
% 0.18/0.44  cnf(c_0_49, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.44  cnf(c_0_50, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_33])).
% 0.18/0.44  fof(c_0_51, plain, ![X10, X11]:(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v2_funct_1(X10)|k2_relat_1(X11)!=k1_relat_1(X10)|k5_relat_1(X11,X10)!=k6_relat_1(k2_relat_1(X10))|X11=k2_funct_1(X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_funct_1])])])).
% 0.18/0.44  cnf(c_0_52, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.44  cnf(c_0_53, negated_conjecture, (k6_relat_1(k2_relat_1(esk3_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_33]), c_0_34])]), c_0_44])).
% 0.18/0.44  cnf(c_0_54, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.44  cnf(c_0_55, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk2_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_20])).
% 0.18/0.44  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_57, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_58, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.18/0.44  cnf(c_0_59, negated_conjecture, (m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.18/0.44  fof(c_0_60, plain, ![X8]:(v1_relat_1(k6_relat_1(X8))&v2_funct_1(k6_relat_1(X8))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.18/0.44  fof(c_0_61, plain, ![X38, X39, X40, X41]:(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X38)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))|(~r2_relset_1(X39,X39,k1_partfun1(X39,X38,X38,X39,X41,X40),k6_partfun1(X39))|k2_relset_1(X38,X39,X40)=X39))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.18/0.44  cnf(c_0_62, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.44  cnf(c_0_63, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X2)!=k1_relat_1(X1)|k5_relat_1(X2,X1)!=k6_relat_1(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.44  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_52])).
% 0.18/0.44  cnf(c_0_65, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3)=k5_relat_1(esk3_0,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_29]), c_0_33])])).
% 0.18/0.44  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.18/0.44  cnf(c_0_67, negated_conjecture, (v2_funct_1(esk4_0)|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_26])]), c_0_57])).
% 0.18/0.44  cnf(c_0_68, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.18/0.44  cnf(c_0_69, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.18/0.44  cnf(c_0_70, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.44  cnf(c_0_71, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.44  cnf(c_0_72, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_62, c_0_23])).
% 0.18/0.44  cnf(c_0_73, negated_conjecture, (k2_funct_1(X1)=esk3_0|k6_relat_1(k2_relat_1(X1))!=k5_relat_1(esk3_0,X1)|k1_relat_1(X1)!=esk2_0|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_33]), c_0_43])]), c_0_64])).
% 0.18/0.44  cnf(c_0_74, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_65, c_0_20])).
% 0.18/0.44  cnf(c_0_75, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k6_relat_1(k2_relat_1(esk4_0))|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_66]), c_0_20])])).
% 0.18/0.44  cnf(c_0_76, negated_conjecture, (v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.18/0.44  cnf(c_0_77, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_70, c_0_23])).
% 0.18/0.44  cnf(c_0_78, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_71])).
% 0.18/0.44  cnf(c_0_79, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.44  cnf(c_0_80, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_32]), c_0_31]), c_0_29]), c_0_33]), c_0_34])]), c_0_35])).
% 0.18/0.44  cnf(c_0_81, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0|k6_relat_1(k2_relat_1(esk4_0))!=k5_relat_1(esk3_0,esk4_0)|k1_relat_1(esk4_0)!=esk2_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_20]), c_0_66])])).
% 0.18/0.44  cnf(c_0_82, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_74, c_0_26])).
% 0.18/0.44  cnf(c_0_83, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k6_relat_1(esk1_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_56]), c_0_26]), c_0_20])]), c_0_57])).
% 0.18/0.44  cnf(c_0_84, negated_conjecture, (k5_relat_1(k2_funct_1(esk4_0),esk4_0)=k6_relat_1(k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.18/0.44  cnf(c_0_85, negated_conjecture, (k2_relset_1(X1,X2,X3)=X2|~v1_funct_2(esk3_0,X2,X1)|~v1_funct_2(X3,X1,X2)|~r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,esk3_0,X3),k6_relat_1(X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(spm,[status(thm)],[c_0_77, c_0_33])).
% 0.18/0.44  cnf(c_0_86, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_78, c_0_49])).
% 0.18/0.44  cnf(c_0_87, negated_conjecture, (k6_relat_1(k1_relat_1(esk3_0))=k6_relat_1(esk1_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_34]), c_0_33]), c_0_43])]), c_0_80])).
% 0.18/0.44  cnf(c_0_88, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0|k6_relat_1(k2_relat_1(esk4_0))!=k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)|k1_relat_1(esk4_0)!=esk2_0|~v2_funct_1(esk4_0)), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.18/0.44  cnf(c_0_89, negated_conjecture, (k6_relat_1(k2_relat_1(esk4_0))=k6_relat_1(esk1_0)|k2_relset_1(esk2_0,esk1_0,esk4_0)!=esk1_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_76])]), c_0_84])).
% 0.18/0.44  cnf(c_0_90, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_26]), c_0_31]), c_0_56]), c_0_68]), c_0_86]), c_0_29]), c_0_20])])).
% 0.18/0.44  cnf(c_0_91, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_76]), c_0_20]), c_0_66])])).
% 0.18/0.44  cnf(c_0_92, negated_conjecture, (k2_funct_1(X1)=esk4_0|k6_relat_1(k2_relat_1(X1))!=k5_relat_1(esk4_0,X1)|k1_relat_1(X1)!=k2_relat_1(esk4_0)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_20]), c_0_66])])).
% 0.18/0.44  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_87]), c_0_52])).
% 0.18/0.44  cnf(c_0_94, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.44  cnf(c_0_95, negated_conjecture, (k1_partfun1(esk2_0,esk1_0,X1,X2,esk4_0,X3)=k5_relat_1(esk4_0,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_26]), c_0_20])])).
% 0.18/0.44  cnf(c_0_96, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0|k6_relat_1(k2_relat_1(esk4_0))!=k6_relat_1(esk1_0)|k1_relat_1(esk4_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_68]), c_0_76])])).
% 0.18/0.44  cnf(c_0_97, negated_conjecture, (k6_relat_1(k2_relat_1(esk4_0))=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.18/0.44  cnf(c_0_98, negated_conjecture, (k6_relat_1(k1_relat_1(esk4_0))=k6_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_90]), c_0_91]), c_0_56]), c_0_26]), c_0_20]), c_0_76])]), c_0_57])).
% 0.18/0.44  cnf(c_0_99, negated_conjecture, (k5_relat_1(esk4_0,esk3_0)!=k6_relat_1(esk2_0)|k2_relat_1(esk4_0)!=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_64]), c_0_93]), c_0_33]), c_0_34]), c_0_43])]), c_0_94])).
% 0.18/0.44  cnf(c_0_100, negated_conjecture, (k5_relat_1(esk4_0,esk3_0)=k1_partfun1(esk2_0,esk1_0,esk1_0,esk2_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_29]), c_0_33])])).
% 0.18/0.44  cnf(c_0_101, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0|k1_relat_1(esk4_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])])).
% 0.18/0.44  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_98]), c_0_52])).
% 0.18/0.44  cnf(c_0_103, negated_conjecture, (k1_partfun1(esk2_0,esk1_0,esk1_0,esk2_0,esk4_0,esk3_0)!=k6_relat_1(esk2_0)|k2_relat_1(esk4_0)!=esk1_0), inference(rw,[status(thm)],[c_0_99, c_0_100])).
% 0.18/0.44  cnf(c_0_104, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_97]), c_0_52])).
% 0.18/0.44  cnf(c_0_105, negated_conjecture, (k2_funct_1(esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 0.18/0.44  cnf(c_0_106, negated_conjecture, (k1_partfun1(esk2_0,esk1_0,esk1_0,esk2_0,esk4_0,esk3_0)!=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.18/0.44  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_98]), c_0_105]), c_0_100]), c_0_106]), ['proof']).
% 0.18/0.44  # SZS output end CNFRefutation
% 0.18/0.44  # Proof object total steps             : 108
% 0.18/0.44  # Proof object clause steps            : 79
% 0.18/0.44  # Proof object formula steps           : 29
% 0.18/0.44  # Proof object conjectures             : 61
% 0.18/0.44  # Proof object clause conjectures      : 58
% 0.18/0.44  # Proof object formula conjectures     : 3
% 0.18/0.44  # Proof object initial clauses used    : 28
% 0.18/0.44  # Proof object initial formulas used   : 14
% 0.18/0.44  # Proof object generating inferences   : 34
% 0.18/0.44  # Proof object simplifying inferences  : 107
% 0.18/0.44  # Training examples: 0 positive, 0 negative
% 0.18/0.44  # Parsed axioms                        : 17
% 0.18/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.44  # Initial clauses                      : 40
% 0.18/0.44  # Removed in clause preprocessing      : 1
% 0.18/0.44  # Initial clauses in saturation        : 39
% 0.18/0.44  # Processed clauses                    : 372
% 0.18/0.44  # ...of these trivial                  : 2
% 0.18/0.44  # ...subsumed                          : 2
% 0.18/0.44  # ...remaining for further processing  : 367
% 0.18/0.44  # Other redundant clauses eliminated   : 6
% 0.18/0.44  # Clauses deleted for lack of memory   : 0
% 0.18/0.44  # Backward-subsumed                    : 0
% 0.18/0.44  # Backward-rewritten                   : 49
% 0.18/0.44  # Generated clauses                    : 915
% 0.18/0.44  # ...of the previous two non-trivial   : 911
% 0.18/0.44  # Contextual simplify-reflections      : 0
% 0.18/0.44  # Paramodulations                      : 909
% 0.18/0.44  # Factorizations                       : 0
% 0.18/0.44  # Equation resolutions                 : 6
% 0.18/0.44  # Propositional unsat checks           : 0
% 0.18/0.44  #    Propositional check models        : 0
% 0.18/0.44  #    Propositional check unsatisfiable : 0
% 0.18/0.44  #    Propositional clauses             : 0
% 0.18/0.44  #    Propositional clauses after purity: 0
% 0.18/0.44  #    Propositional unsat core size     : 0
% 0.18/0.44  #    Propositional preprocessing time  : 0.000
% 0.18/0.44  #    Propositional encoding time       : 0.000
% 0.18/0.44  #    Propositional solver time         : 0.000
% 0.18/0.44  #    Success case prop preproc time    : 0.000
% 0.18/0.44  #    Success case prop encoding time   : 0.000
% 0.18/0.44  #    Success case prop solver time     : 0.000
% 0.18/0.44  # Current number of processed clauses  : 275
% 0.18/0.44  #    Positive orientable unit clauses  : 110
% 0.18/0.44  #    Positive unorientable unit clauses: 0
% 0.18/0.44  #    Negative unit clauses             : 4
% 0.18/0.44  #    Non-unit-clauses                  : 161
% 0.18/0.44  # Current number of unprocessed clauses: 588
% 0.18/0.44  # ...number of literals in the above   : 2666
% 0.18/0.44  # Current number of archived formulas  : 0
% 0.18/0.44  # Current number of archived clauses   : 89
% 0.18/0.44  # Clause-clause subsumption calls (NU) : 7479
% 0.18/0.44  # Rec. Clause-clause subsumption calls : 558
% 0.18/0.44  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.44  # Unit Clause-clause subsumption calls : 701
% 0.18/0.44  # Rewrite failures with RHS unbound    : 0
% 0.18/0.44  # BW rewrite match attempts            : 447
% 0.18/0.44  # BW rewrite match successes           : 22
% 0.18/0.44  # Condensation attempts                : 0
% 0.18/0.44  # Condensation successes               : 0
% 0.18/0.44  # Termbank termtop insertions          : 52339
% 0.18/0.44  
% 0.18/0.44  # -------------------------------------------------
% 0.18/0.44  # User time                : 0.106 s
% 0.18/0.44  # System time              : 0.006 s
% 0.18/0.44  # Total time               : 0.112 s
% 0.18/0.44  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
