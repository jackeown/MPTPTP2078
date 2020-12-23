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
% DateTime   : Thu Dec  3 11:02:11 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 322 expanded)
%              Number of clauses        :   57 ( 124 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (1687 expanded)
%              Number of equality atoms :   48 (  85 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t29_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(t26_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_17,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X52,X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X53,X52)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))
      | ~ r2_relset_1(X53,X53,k1_partfun1(X53,X52,X52,X53,X55,X54),k6_partfun1(X53))
      | k2_relset_1(X52,X53,X54) = X53 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

fof(c_0_18,plain,(
    ! [X51] : k6_partfun1(X51) = k6_relat_1(X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
             => ( v2_funct_1(X3)
                & v2_funct_2(X4,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_funct_2])).

cnf(c_0_20,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))
    & ( ~ v2_funct_1(esk4_0)
      | ~ v2_funct_2(esk5_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_24,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_32,plain,(
    ! [X43,X44] :
      ( ( ~ v2_funct_2(X44,X43)
        | k2_relat_1(X44) = X43
        | ~ v1_relat_1(X44)
        | ~ v5_relat_1(X44,X43) )
      & ( k2_relat_1(X44) != X43
        | v2_funct_2(X44,X43)
        | ~ v1_relat_1(X44)
        | ~ v5_relat_1(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,X1) = esk2_0
    | ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,X1),k6_relat_1(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X17,X18,X19] :
      ( ( v4_relat_1(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v5_relat_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_40,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_43,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,plain,(
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

fof(c_0_45,plain,(
    ! [X42] : m1_subset_1(k6_relat_1(X42),k1_zfmisc_1(k2_zfmisc_1(X42,X42))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_46,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_partfun1(X45,X46,X47,X48,X49,X50) = k5_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_47,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k4_relset_1(X32,X33,X34,X35,X36,X37) = k5_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_48,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( ( X58 = k1_xboole_0
        | v2_funct_1(X59)
        | ~ v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X57 != k1_xboole_0
        | v2_funct_1(X59)
        | ~ v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_2(esk5_0,X1)
    | esk2_0 != X1
    | ~ v5_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_50,negated_conjecture,
    ( v5_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_29])).

cnf(c_0_51,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k4_relset_1(X23,X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X23,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_55,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_56,plain,(
    ! [X13] : v2_funct_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

fof(c_0_57,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | X7 = X8
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_58,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_xboole_0(X20)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_xboole_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_funct_1(esk4_0)
    | ~ v2_funct_2(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( v2_funct_2(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_50])])).

cnf(c_0_62,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k1_partfun1(X1,X2,esk3_0,esk2_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_36])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k4_relset_1(X1,X2,esk3_0,esk2_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_29])).

cnf(c_0_66,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(k1_partfun1(X2,esk3_0,esk3_0,esk2_0,X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_34]),c_0_36])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_71,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_37])).

cnf(c_0_72,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_25]),c_0_27])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k4_relset_1(X1,X2,esk3_0,esk2_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( k4_relset_1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_25])).

cnf(c_0_75,plain,
    ( v2_funct_1(X1)
    | ~ v1_xboole_0(k6_relat_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_52])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v2_funct_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_27]),c_0_25])]),c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k5_relat_1(esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_25]),c_0_74])).

cnf(c_0_80,plain,
    ( v2_funct_1(X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v2_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(esk4_0,esk5_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v2_funct_2(esk5_0,esk2_0)
    | ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_25])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_66])])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_61])])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_90,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_86,c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.46  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.18/0.46  # and selection function SelectNewComplexAHP.
% 0.18/0.46  #
% 0.18/0.46  # Preprocessing time       : 0.029 s
% 0.18/0.46  # Presaturation interreduction done
% 0.18/0.46  
% 0.18/0.46  # Proof found!
% 0.18/0.46  # SZS status Theorem
% 0.18/0.46  # SZS output start CNFRefutation
% 0.18/0.46  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 0.18/0.46  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.18/0.46  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 0.18/0.46  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.18/0.46  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.46  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.18/0.46  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.46  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.18/0.46  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.18/0.46  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.18/0.46  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.18/0.46  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 0.18/0.46  fof(dt_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 0.18/0.46  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 0.18/0.46  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.18/0.46  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.18/0.46  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.46  fof(c_0_17, plain, ![X52, X53, X54, X55]:(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))|(~r2_relset_1(X53,X53,k1_partfun1(X53,X52,X52,X53,X55,X54),k6_partfun1(X53))|k2_relset_1(X52,X53,X54)=X53))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.18/0.46  fof(c_0_18, plain, ![X51]:k6_partfun1(X51)=k6_relat_1(X51), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.18/0.46  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.18/0.46  cnf(c_0_20, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.46  cnf(c_0_21, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.46  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))&(~v2_funct_1(esk4_0)|~v2_funct_2(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.18/0.46  fof(c_0_23, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.18/0.46  cnf(c_0_24, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.46  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_28, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.46  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_30, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  fof(c_0_31, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.46  fof(c_0_32, plain, ![X43, X44]:((~v2_funct_2(X44,X43)|k2_relat_1(X44)=X43|(~v1_relat_1(X44)|~v5_relat_1(X44,X43)))&(k2_relat_1(X44)!=X43|v2_funct_2(X44,X43)|(~v1_relat_1(X44)|~v5_relat_1(X44,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.18/0.46  cnf(c_0_33, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,X1)=esk2_0|~v1_funct_2(X1,esk3_0,esk2_0)|~v1_funct_1(X1)|~r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,X1),k6_relat_1(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.18/0.46  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_35, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.46  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_37, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_30, c_0_21])).
% 0.18/0.46  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.46  fof(c_0_39, plain, ![X17, X18, X19]:((v4_relat_1(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(v5_relat_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.46  cnf(c_0_40, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.46  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_29])])).
% 0.18/0.46  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 0.18/0.46  cnf(c_0_43, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.46  fof(c_0_44, plain, ![X38, X39, X40, X41]:((~r2_relset_1(X38,X39,X40,X41)|X40=X41|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(X40!=X41|r2_relset_1(X38,X39,X40,X41)|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.18/0.46  fof(c_0_45, plain, ![X42]:m1_subset_1(k6_relat_1(X42),k1_zfmisc_1(k2_zfmisc_1(X42,X42))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.18/0.46  fof(c_0_46, plain, ![X45, X46, X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_partfun1(X45,X46,X47,X48,X49,X50)=k5_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.18/0.46  fof(c_0_47, plain, ![X32, X33, X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k4_relset_1(X32,X33,X34,X35,X36,X37)=k5_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.18/0.46  fof(c_0_48, plain, ![X56, X57, X58, X59, X60]:((X58=k1_xboole_0|v2_funct_1(X59)|~v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(X57!=k1_xboole_0|v2_funct_1(X59)|~v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.18/0.46  cnf(c_0_49, negated_conjecture, (v2_funct_2(esk5_0,X1)|esk2_0!=X1|~v5_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.18/0.46  cnf(c_0_50, negated_conjecture, (v5_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_29])).
% 0.18/0.46  cnf(c_0_51, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.46  cnf(c_0_52, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.46  cnf(c_0_53, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.46  fof(c_0_54, plain, ![X23, X24, X25, X26, X27, X28]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|m1_subset_1(k4_relset_1(X23,X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X23,X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).
% 0.18/0.46  cnf(c_0_55, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.46  fof(c_0_56, plain, ![X13]:v2_funct_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.18/0.46  fof(c_0_57, plain, ![X7, X8]:(~v1_xboole_0(X7)|X7=X8|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.18/0.46  fof(c_0_58, plain, ![X20, X21, X22]:(~v1_xboole_0(X20)|(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_xboole_0(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.18/0.46  cnf(c_0_59, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.46  cnf(c_0_60, negated_conjecture, (~v2_funct_1(esk4_0)|~v2_funct_2(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.46  cnf(c_0_61, negated_conjecture, (v2_funct_2(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_50])])).
% 0.18/0.46  cnf(c_0_62, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.46  cnf(c_0_63, negated_conjecture, (k1_partfun1(X1,X2,esk3_0,esk2_0,X3,esk5_0)=k5_relat_1(X3,esk5_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_36])])).
% 0.18/0.46  cnf(c_0_64, plain, (m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.46  cnf(c_0_65, negated_conjecture, (k4_relset_1(X1,X2,esk3_0,esk2_0,X3,esk5_0)=k5_relat_1(X3,esk5_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_55, c_0_29])).
% 0.18/0.46  cnf(c_0_66, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.46  cnf(c_0_67, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.46  cnf(c_0_68, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.46  cnf(c_0_69, negated_conjecture, (esk2_0=k1_xboole_0|v2_funct_1(X1)|~v1_funct_2(X1,X2,esk3_0)|~v1_funct_1(X1)|~v2_funct_1(k1_partfun1(X2,esk3_0,esk3_0,esk2_0,X1,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_34]), c_0_36])])).
% 0.18/0.46  cnf(c_0_70, negated_conjecture, (~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.18/0.46  cnf(c_0_71, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_62, c_0_37])).
% 0.18/0.46  cnf(c_0_72, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_25]), c_0_27])])).
% 0.18/0.46  cnf(c_0_73, negated_conjecture, (m1_subset_1(k4_relset_1(X1,X2,esk3_0,esk2_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_29])).
% 0.18/0.46  cnf(c_0_74, negated_conjecture, (k4_relset_1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k5_relat_1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_25])).
% 0.18/0.46  cnf(c_0_75, plain, (v2_funct_1(X1)|~v1_xboole_0(k6_relat_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.46  cnf(c_0_76, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_52])).
% 0.18/0.46  cnf(c_0_77, negated_conjecture, (esk2_0=k1_xboole_0|~v2_funct_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_26]), c_0_27]), c_0_25])]), c_0_70])).
% 0.18/0.46  cnf(c_0_78, negated_conjecture, (k5_relat_1(esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_72])).
% 0.18/0.46  cnf(c_0_79, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_25]), c_0_74])).
% 0.18/0.46  cnf(c_0_80, plain, (v2_funct_1(X1)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.18/0.46  cnf(c_0_81, negated_conjecture, (esk2_0=k1_xboole_0|~v2_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_77, c_0_72])).
% 0.18/0.46  cnf(c_0_82, negated_conjecture, (k5_relat_1(esk4_0,esk5_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.18/0.46  cnf(c_0_83, negated_conjecture, (~v2_funct_2(esk5_0,esk2_0)|~v1_xboole_0(esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_60, c_0_80])).
% 0.18/0.46  cnf(c_0_84, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_25])).
% 0.18/0.46  cnf(c_0_85, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_66])])).
% 0.18/0.46  cnf(c_0_86, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.46  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(esk4_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_61])])).
% 0.18/0.46  cnf(c_0_88, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 0.18/0.46  cnf(c_0_89, negated_conjecture, (~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.18/0.46  cnf(c_0_90, plain, ($false), inference(sr,[status(thm)],[c_0_86, c_0_89]), ['proof']).
% 0.18/0.46  # SZS output end CNFRefutation
% 0.18/0.46  # Proof object total steps             : 91
% 0.18/0.46  # Proof object clause steps            : 57
% 0.18/0.46  # Proof object formula steps           : 34
% 0.18/0.46  # Proof object conjectures             : 38
% 0.18/0.46  # Proof object clause conjectures      : 35
% 0.18/0.46  # Proof object formula conjectures     : 3
% 0.18/0.46  # Proof object initial clauses used    : 24
% 0.18/0.46  # Proof object initial formulas used   : 17
% 0.18/0.46  # Proof object generating inferences   : 22
% 0.18/0.46  # Proof object simplifying inferences  : 44
% 0.18/0.46  # Training examples: 0 positive, 0 negative
% 0.18/0.46  # Parsed axioms                        : 19
% 0.18/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.46  # Initial clauses                      : 31
% 0.18/0.46  # Removed in clause preprocessing      : 1
% 0.18/0.46  # Initial clauses in saturation        : 30
% 0.18/0.46  # Processed clauses                    : 1385
% 0.18/0.46  # ...of these trivial                  : 0
% 0.18/0.46  # ...subsumed                          : 917
% 0.18/0.46  # ...remaining for further processing  : 468
% 0.18/0.46  # Other redundant clauses eliminated   : 6
% 0.18/0.46  # Clauses deleted for lack of memory   : 0
% 0.18/0.46  # Backward-subsumed                    : 20
% 0.18/0.46  # Backward-rewritten                   : 206
% 0.18/0.46  # Generated clauses                    : 3205
% 0.18/0.46  # ...of the previous two non-trivial   : 3260
% 0.18/0.46  # Contextual simplify-reflections      : 5
% 0.18/0.46  # Paramodulations                      : 3188
% 0.18/0.46  # Factorizations                       : 0
% 0.18/0.46  # Equation resolutions                 : 10
% 0.18/0.46  # Propositional unsat checks           : 0
% 0.18/0.46  #    Propositional check models        : 0
% 0.18/0.46  #    Propositional check unsatisfiable : 0
% 0.18/0.46  #    Propositional clauses             : 0
% 0.18/0.46  #    Propositional clauses after purity: 0
% 0.18/0.46  #    Propositional unsat core size     : 0
% 0.18/0.46  #    Propositional preprocessing time  : 0.000
% 0.18/0.46  #    Propositional encoding time       : 0.000
% 0.18/0.46  #    Propositional solver time         : 0.000
% 0.18/0.46  #    Success case prop preproc time    : 0.000
% 0.18/0.46  #    Success case prop encoding time   : 0.000
% 0.18/0.46  #    Success case prop solver time     : 0.000
% 0.18/0.46  # Current number of processed clauses  : 204
% 0.18/0.46  #    Positive orientable unit clauses  : 17
% 0.18/0.46  #    Positive unorientable unit clauses: 0
% 0.18/0.46  #    Negative unit clauses             : 2
% 0.18/0.46  #    Non-unit-clauses                  : 185
% 0.18/0.46  # Current number of unprocessed clauses: 1889
% 0.18/0.46  # ...number of literals in the above   : 9315
% 0.18/0.46  # Current number of archived formulas  : 0
% 0.18/0.46  # Current number of archived clauses   : 264
% 0.18/0.46  # Clause-clause subsumption calls (NU) : 37942
% 0.18/0.46  # Rec. Clause-clause subsumption calls : 12769
% 0.18/0.46  # Non-unit clause-clause subsumptions  : 941
% 0.18/0.46  # Unit Clause-clause subsumption calls : 330
% 0.18/0.46  # Rewrite failures with RHS unbound    : 0
% 0.18/0.46  # BW rewrite match attempts            : 57
% 0.18/0.46  # BW rewrite match successes           : 10
% 0.18/0.46  # Condensation attempts                : 0
% 0.18/0.46  # Condensation successes               : 0
% 0.18/0.46  # Termbank termtop insertions          : 48605
% 0.18/0.46  
% 0.18/0.46  # -------------------------------------------------
% 0.18/0.46  # User time                : 0.120 s
% 0.18/0.46  # System time              : 0.008 s
% 0.18/0.46  # Total time               : 0.128 s
% 0.18/0.46  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
