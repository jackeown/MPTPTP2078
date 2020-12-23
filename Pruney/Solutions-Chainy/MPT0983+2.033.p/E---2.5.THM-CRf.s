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
% DateTime   : Thu Dec  3 11:02:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 319 expanded)
%              Number of clauses        :   56 ( 122 expanded)
%              Number of leaves         :   19 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :  289 (1683 expanded)
%              Number of equality atoms :   62 (  98 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

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

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,X49,X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ v1_funct_1(X52)
      | ~ v1_funct_2(X52,X50,X49)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
      | ~ r2_relset_1(X50,X50,k1_partfun1(X50,X49,X49,X50,X52,X51),k6_partfun1(X50))
      | k2_relset_1(X49,X50,X51) = X50 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

fof(c_0_20,plain,(
    ! [X48] : k6_partfun1(X48) = k6_relat_1(X48) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_21,negated_conjecture,(
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

cnf(c_0_22,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))
    & ( ~ v2_funct_1(esk3_0)
      | ~ v2_funct_2(esk4_0,esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_26,plain,(
    ! [X40,X41] :
      ( ( ~ v2_funct_2(X41,X40)
        | k2_relat_1(X41) = X40
        | ~ v1_relat_1(X41)
        | ~ v5_relat_1(X41,X40) )
      & ( k2_relat_1(X41) != X40
        | v2_funct_2(X41,X40)
        | ~ v1_relat_1(X41)
        | ~ v5_relat_1(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X17,X18,X19] :
      ( ( v4_relat_1(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v5_relat_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_35,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_36,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ r2_relset_1(X35,X36,X37,X38)
        | X37 = X38
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r2_relset_1(X35,X36,X37,X38)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_37,plain,(
    ! [X39] : m1_subset_1(k6_relat_1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_38,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_partfun1(X42,X43,X44,X45,X46,X47) = k5_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_39,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k4_relset_1(X29,X30,X31,X32,X33,X34) = k5_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_40,plain,(
    ! [X53,X54,X55,X56,X57] :
      ( ( X55 = k1_xboole_0
        | v2_funct_1(X56)
        | ~ v2_funct_1(k1_partfun1(X53,X54,X54,X55,X56,X57))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X53,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( X54 != k1_xboole_0
        | v2_funct_1(X56)
        | ~ v2_funct_1(k1_partfun1(X53,X54,X54,X55,X56,X57))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X53,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_41,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,X1) = esk1_0
    | ~ v1_funct_2(X1,esk2_0,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,X1),k6_relat_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_52,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | m1_subset_1(k4_relset_1(X20,X21,X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(X20,X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_53,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( v5_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_59,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k1_partfun1(X1,X2,esk2_0,esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_45])])).

cnf(c_0_61,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k4_relset_1(X1,X2,esk2_0,esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(k1_partfun1(X2,esk2_0,esk2_0,esk1_0,X1,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_43]),c_0_45])])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_funct_1(esk3_0)
    | ~ v2_funct_2(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( v2_funct_2(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_28]),c_0_30])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k4_relset_1(X1,X2,esk2_0,esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( k4_relset_1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_28])).

fof(c_0_70,plain,(
    ! [X13] : v2_funct_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

fof(c_0_71,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | X7 = X8
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_72,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_73,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v2_funct_1(esk3_0)
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_29]),c_0_30]),c_0_28])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_75,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_28]),c_0_69])).

fof(c_0_77,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_78,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_67]),c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( v2_funct_1(X1)
    | ~ v1_xboole_0(k6_relat_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_28])).

cnf(c_0_88,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_78])])).

cnf(c_0_89,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( v2_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_86])])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.20/0.40  # and selection function SelectNewComplexAHP.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.031 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 0.20/0.40  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.40  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 0.20/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.40  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.20/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.40  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.40  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.20/0.40  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.20/0.40  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.20/0.40  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 0.20/0.40  fof(dt_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 0.20/0.40  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 0.20/0.40  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.20/0.40  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.40  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.20/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.40  fof(c_0_19, plain, ![X49, X50, X51, X52]:(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X50)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|(~r2_relset_1(X50,X50,k1_partfun1(X50,X49,X49,X50,X52,X51),k6_partfun1(X50))|k2_relset_1(X49,X50,X51)=X50))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.20/0.40  fof(c_0_20, plain, ![X48]:k6_partfun1(X48)=k6_relat_1(X48), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.40  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.20/0.40  cnf(c_0_22, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_23, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))&(~v2_funct_1(esk3_0)|~v2_funct_2(esk4_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.40  fof(c_0_25, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.40  fof(c_0_26, plain, ![X40, X41]:((~v2_funct_2(X41,X40)|k2_relat_1(X41)=X40|(~v1_relat_1(X41)|~v5_relat_1(X41,X40)))&(k2_relat_1(X41)!=X40|v2_funct_2(X41,X40)|(~v1_relat_1(X41)|~v5_relat_1(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.20/0.40  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_31, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  fof(c_0_34, plain, ![X17, X18, X19]:((v4_relat_1(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(v5_relat_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.40  fof(c_0_35, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.40  fof(c_0_36, plain, ![X35, X36, X37, X38]:((~r2_relset_1(X35,X36,X37,X38)|X37=X38|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(X37!=X38|r2_relset_1(X35,X36,X37,X38)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.40  fof(c_0_37, plain, ![X39]:m1_subset_1(k6_relat_1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.20/0.40  fof(c_0_38, plain, ![X42, X43, X44, X45, X46, X47]:(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k1_partfun1(X42,X43,X44,X45,X46,X47)=k5_relat_1(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.20/0.40  fof(c_0_39, plain, ![X29, X30, X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k4_relset_1(X29,X30,X31,X32,X33,X34)=k5_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.20/0.40  fof(c_0_40, plain, ![X53, X54, X55, X56, X57]:((X55=k1_xboole_0|v2_funct_1(X56)|~v2_funct_1(k1_partfun1(X53,X54,X54,X55,X56,X57))|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))|(~v1_funct_1(X56)|~v1_funct_2(X56,X53,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))))&(X54!=k1_xboole_0|v2_funct_1(X56)|~v2_funct_1(k1_partfun1(X53,X54,X54,X55,X56,X57))|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))|(~v1_funct_1(X56)|~v1_funct_2(X56,X53,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.20/0.40  cnf(c_0_41, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,X1)=esk1_0|~v1_funct_2(X1,esk2_0,esk1_0)|~v1_funct_1(X1)|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,X1),k6_relat_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_33, c_0_23])).
% 0.20/0.40  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_48, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_49, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_50, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_51, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  fof(c_0_52, plain, ![X20, X21, X22, X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|m1_subset_1(k4_relset_1(X20,X21,X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(X20,X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).
% 0.20/0.40  cnf(c_0_53, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_54, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_55, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_32])])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (v5_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_32])).
% 0.20/0.40  cnf(c_0_59, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (k1_partfun1(X1,X2,esk2_0,esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_45])])).
% 0.20/0.40  cnf(c_0_61, plain, (m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (k4_relset_1(X1,X2,esk2_0,esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_53, c_0_32])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (esk1_0=k1_xboole_0|v2_funct_1(X1)|~v1_funct_2(X1,X2,esk2_0)|~v1_funct_1(X1)|~v2_funct_1(k1_partfun1(X2,esk2_0,esk2_0,esk1_0,X1,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_32]), c_0_43]), c_0_45])])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (~v2_funct_1(esk3_0)|~v2_funct_2(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (v2_funct_2(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_28]), c_0_30])])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (m1_subset_1(k4_relset_1(X1,X2,esk2_0,esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_61, c_0_32])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (k4_relset_1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_28])).
% 0.20/0.40  fof(c_0_70, plain, ![X13]:v2_funct_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.20/0.40  fof(c_0_71, plain, ![X7, X8]:(~v1_xboole_0(X7)|X7=X8|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.20/0.40  fof(c_0_72, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (esk1_0=k1_xboole_0|v2_funct_1(esk3_0)|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_29]), c_0_30]), c_0_28])])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_67])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_28]), c_0_69])).
% 0.20/0.40  fof(c_0_77, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.40  cnf(c_0_78, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.40  cnf(c_0_79, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.40  cnf(c_0_80, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (esk1_0=k1_xboole_0|~v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_67]), c_0_74])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.20/0.40  cnf(c_0_83, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.40  cnf(c_0_84, plain, (v2_funct_1(X1)|~v1_xboole_0(k6_relat_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.40  cnf(c_0_85, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.20/0.40  cnf(c_0_86, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_80, c_0_28])).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_78])])).
% 0.20/0.40  cnf(c_0_89, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_83])).
% 0.20/0.40  cnf(c_0_90, plain, (v2_funct_1(X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 0.20/0.40  cnf(c_0_91, negated_conjecture, (v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_86])])).
% 0.20/0.40  cnf(c_0_92, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_74]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 93
% 0.20/0.40  # Proof object clause steps            : 56
% 0.20/0.40  # Proof object formula steps           : 37
% 0.20/0.40  # Proof object conjectures             : 35
% 0.20/0.40  # Proof object clause conjectures      : 32
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 26
% 0.20/0.40  # Proof object initial formulas used   : 19
% 0.20/0.40  # Proof object generating inferences   : 22
% 0.20/0.40  # Proof object simplifying inferences  : 42
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 19
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 32
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 31
% 0.20/0.40  # Processed clauses                    : 344
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 109
% 0.20/0.40  # ...remaining for further processing  : 234
% 0.20/0.40  # Other redundant clauses eliminated   : 3
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 9
% 0.20/0.40  # Backward-rewritten                   : 90
% 0.20/0.40  # Generated clauses                    : 475
% 0.20/0.40  # ...of the previous two non-trivial   : 524
% 0.20/0.40  # Contextual simplify-reflections      : 3
% 0.20/0.40  # Paramodulations                      : 467
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 8
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 103
% 0.20/0.40  #    Positive orientable unit clauses  : 30
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 72
% 0.20/0.40  # Current number of unprocessed clauses: 233
% 0.20/0.40  # ...number of literals in the above   : 875
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 131
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 4153
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1525
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 121
% 0.20/0.40  # Unit Clause-clause subsumption calls : 46
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 79
% 0.20/0.40  # BW rewrite match successes           : 10
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 10475
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
