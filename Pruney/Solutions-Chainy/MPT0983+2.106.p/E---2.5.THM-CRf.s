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
% DateTime   : Thu Dec  3 11:02:24 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 292 expanded)
%              Number of clauses        :   54 ( 111 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  293 (1481 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

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

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

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

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))
    & ( ~ v2_funct_1(esk4_0)
      | ~ v2_funct_2(esk5_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_20,plain,(
    ! [X52] : k6_partfun1(X52) = k6_relat_1(X52) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_21,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | m1_subset_1(k4_relset_1(X24,X25,X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(X24,X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

fof(c_0_22,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k4_relset_1(X33,X34,X35,X36,X37,X38) = k5_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X53,X54,X55,X56] :
      ( ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X53,X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X54,X53)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
      | ~ r2_relset_1(X54,X54,k1_partfun1(X54,X53,X53,X54,X56,X55),k6_partfun1(X54))
      | k2_relset_1(X53,X54,X55) = X54 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).

fof(c_0_26,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ r2_relset_1(X39,X40,X41,X42)
        | X41 = X42
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != X42
        | r2_relset_1(X39,X40,X41,X42)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X43] : m1_subset_1(k6_relat_1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_30,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( ( ~ v2_funct_2(X45,X44)
        | k2_relat_1(X45) = X44
        | ~ v1_relat_1(X45)
        | ~ v5_relat_1(X45,X44) )
      & ( k2_relat_1(X45) != X44
        | v2_funct_2(X45,X44)
        | ~ v1_relat_1(X45)
        | ~ v5_relat_1(X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_33,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_37,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_39,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_41,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | ~ v1_funct_1(X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_partfun1(X46,X47,X48,X49,X50,X51) = k5_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_funct_1(esk4_0)
    | ~ v2_funct_2(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_49,plain,
    ( k2_relset_1(X2,X3,X1) = X3
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X3,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_55,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | X7 = X8
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_57,plain,(
    ! [X57,X58,X59,X60,X61] :
      ( ( X59 = k1_xboole_0
        | v2_funct_1(X60)
        | ~ v2_funct_1(k1_partfun1(X57,X58,X58,X59,X60,X61))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X58 != k1_xboole_0
        | v2_funct_1(X60)
        | ~ v2_funct_1(k1_partfun1(X57,X58,X58,X59,X60,X61))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_58,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_59,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( k2_relat_1(esk5_0) != esk2_0
    | ~ v5_relat_1(esk5_0,esk2_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_62,negated_conjecture,
    ( v5_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_63,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( k2_relset_1(esk3_0,esk2_0,esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_34])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_41])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( k5_relat_1(esk4_0,esk5_0) = k6_relat_1(esk2_0)
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_52]),c_0_34]),c_0_54])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

fof(c_0_70,plain,(
    ! [X17] :
      ( v1_relat_1(k6_relat_1(X17))
      & v2_funct_1(k6_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_71,negated_conjecture,
    ( k2_relat_1(esk5_0) != esk2_0
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_34])])).

cnf(c_0_73,plain,
    ( v1_xboole_0(k4_relset_1(X1,X2,X3,X4,X5,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_74,plain,
    ( X1 = k6_relat_1(X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ v1_funct_2(X2,X5,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_59])).

cnf(c_0_77,negated_conjecture,
    ( k5_relat_1(esk4_0,esk5_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_78,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_80,plain,
    ( v1_xboole_0(k5_relat_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ v1_xboole_0(X5) ),
    inference(spm,[status(thm)],[c_0_73,c_0_31])).

cnf(c_0_81,negated_conjecture,
    ( k6_relat_1(X1) = esk4_0
    | ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(esk5_0,X2,X1)
    | ~ v1_funct_2(esk4_0,X3,X2)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_53]),c_0_52]),c_0_78])]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(k5_relat_1(X1,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_81]),c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,X1,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_51]),c_0_34])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_54]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_50]),c_0_54])])).

cnf(c_0_88,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 0.47/0.63  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.036 s
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 0.47/0.63  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.47/0.63  fof(dt_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 0.47/0.63  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.47/0.63  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.47/0.63  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.47/0.63  fof(t24_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X2,X2,k1_partfun1(X2,X1,X1,X2,X4,X3),k6_partfun1(X2))=>k2_relset_1(X1,X2,X3)=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 0.47/0.63  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.47/0.63  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.47/0.63  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.47/0.63  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.47/0.63  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.47/0.63  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.47/0.63  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.47/0.63  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.47/0.63  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 0.47/0.63  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.47/0.63  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.47/0.63  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.47/0.63  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))&(~v2_funct_1(esk4_0)|~v2_funct_2(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.47/0.63  fof(c_0_20, plain, ![X52]:k6_partfun1(X52)=k6_relat_1(X52), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.47/0.63  fof(c_0_21, plain, ![X24, X25, X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|m1_subset_1(k4_relset_1(X24,X25,X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(X24,X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).
% 0.47/0.63  fof(c_0_22, plain, ![X33, X34, X35, X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k4_relset_1(X33,X34,X35,X36,X37,X38)=k5_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.47/0.63  fof(c_0_23, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.47/0.63  fof(c_0_24, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.47/0.63  fof(c_0_25, plain, ![X53, X54, X55, X56]:(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X54)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|(~r2_relset_1(X54,X54,k1_partfun1(X54,X53,X53,X54,X56,X55),k6_partfun1(X54))|k2_relset_1(X53,X54,X55)=X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_2])])])).
% 0.47/0.63  fof(c_0_26, plain, ![X39, X40, X41, X42]:((~r2_relset_1(X39,X40,X41,X42)|X41=X42|(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(X41!=X42|r2_relset_1(X39,X40,X41,X42)|(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.47/0.64  cnf(c_0_27, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_28, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.64  fof(c_0_29, plain, ![X43]:m1_subset_1(k6_relat_1(X43),k1_zfmisc_1(k2_zfmisc_1(X43,X43))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.47/0.64  cnf(c_0_30, plain, (m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.64  cnf(c_0_31, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.64  fof(c_0_32, plain, ![X44, X45]:((~v2_funct_2(X45,X44)|k2_relat_1(X45)=X44|(~v1_relat_1(X45)|~v5_relat_1(X45,X44)))&(k2_relat_1(X45)!=X44|v2_funct_2(X45,X44)|(~v1_relat_1(X45)|~v5_relat_1(X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.47/0.64  cnf(c_0_33, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.64  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.64  fof(c_0_36, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.47/0.64  cnf(c_0_37, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_partfun1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.64  fof(c_0_38, plain, ![X21, X22, X23]:(~v1_xboole_0(X21)|(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|v1_xboole_0(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.47/0.64  cnf(c_0_39, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.64  cnf(c_0_40, negated_conjecture, (r2_relset_1(esk2_0,esk2_0,k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.64  cnf(c_0_41, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.64  fof(c_0_42, plain, ![X46, X47, X48, X49, X50, X51]:(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_partfun1(X46,X47,X48,X49,X50,X51)=k5_relat_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.47/0.64  cnf(c_0_43, plain, (m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.47/0.64  cnf(c_0_44, negated_conjecture, (~v2_funct_1(esk4_0)|~v2_funct_2(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_45, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.64  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.47/0.64  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.64  fof(c_0_48, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k2_relset_1(X30,X31,X32)=k2_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.47/0.64  cnf(c_0_49, plain, (k2_relset_1(X2,X3,X1)=X3|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X3,X2)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_relset_1(X3,X3,k1_partfun1(X3,X2,X2,X3,X4,X1),k6_relat_1(X3))), inference(rw,[status(thm)],[c_0_37, c_0_28])).
% 0.47/0.64  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.64  fof(c_0_55, plain, ![X7, X8]:(~v1_xboole_0(X7)|X7=X8|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.47/0.64  cnf(c_0_56, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.64  fof(c_0_57, plain, ![X57, X58, X59, X60, X61]:((X59=k1_xboole_0|v2_funct_1(X60)|~v2_funct_1(k1_partfun1(X57,X58,X58,X59,X60,X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))))&(X58!=k1_xboole_0|v2_funct_1(X60)|~v2_funct_1(k1_partfun1(X57,X58,X58,X59,X60,X61))|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.47/0.64  cnf(c_0_58, negated_conjecture, (k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k1_partfun1(esk2_0,esk3_0,esk3_0,esk2_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.47/0.64  cnf(c_0_59, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.47/0.64  cnf(c_0_60, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 0.47/0.64  cnf(c_0_61, negated_conjecture, (k2_relat_1(esk5_0)!=esk2_0|~v5_relat_1(esk5_0,esk2_0)|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.47/0.64  cnf(c_0_62, negated_conjecture, (v5_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 0.47/0.64  cnf(c_0_63, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.47/0.64  cnf(c_0_64, negated_conjecture, (k2_relset_1(esk3_0,esk2_0,esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_34])])).
% 0.47/0.64  cnf(c_0_65, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.47/0.64  cnf(c_0_66, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_41])).
% 0.47/0.64  cnf(c_0_67, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.47/0.64  cnf(c_0_68, negated_conjecture, (k5_relat_1(esk4_0,esk5_0)=k6_relat_1(esk2_0)|~m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_53]), c_0_52]), c_0_34]), c_0_54])])).
% 0.47/0.64  cnf(c_0_69, negated_conjecture, (m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 0.47/0.64  fof(c_0_70, plain, ![X17]:(v1_relat_1(k6_relat_1(X17))&v2_funct_1(k6_relat_1(X17))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.47/0.64  cnf(c_0_71, negated_conjecture, (k2_relat_1(esk5_0)!=esk2_0|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.47/0.64  cnf(c_0_72, negated_conjecture, (k2_relat_1(esk5_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_34])])).
% 0.47/0.64  cnf(c_0_73, plain, (v1_xboole_0(k4_relset_1(X1,X2,X3,X4,X5,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_56, c_0_30])).
% 0.47/0.64  cnf(c_0_74, plain, (X1=k6_relat_1(X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.47/0.64  cnf(c_0_75, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_54])).
% 0.47/0.64  cnf(c_0_76, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v1_funct_2(X3,X4,X1)|~v1_funct_2(X2,X5,X4)|~v1_funct_1(X3)|~v1_funct_1(X2)|~v2_funct_1(k5_relat_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))), inference(spm,[status(thm)],[c_0_67, c_0_59])).
% 0.47/0.64  cnf(c_0_77, negated_conjecture, (k5_relat_1(esk4_0,esk5_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.47/0.64  cnf(c_0_78, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.47/0.64  cnf(c_0_79, negated_conjecture, (~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.47/0.64  cnf(c_0_80, plain, (v1_xboole_0(k5_relat_1(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|~v1_xboole_0(X5)), inference(spm,[status(thm)],[c_0_73, c_0_31])).
% 0.47/0.64  cnf(c_0_81, negated_conjecture, (k6_relat_1(X1)=esk4_0|~v1_xboole_0(esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.47/0.64  cnf(c_0_82, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(esk5_0,X2,X1)|~v1_funct_2(esk4_0,X3,X2)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_53]), c_0_52]), c_0_78])]), c_0_79])).
% 0.47/0.64  cnf(c_0_83, negated_conjecture, (v1_xboole_0(k5_relat_1(X1,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_80, c_0_34])).
% 0.47/0.64  cnf(c_0_84, negated_conjecture, (~v1_xboole_0(esk2_0)|~v1_xboole_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_81]), c_0_79])).
% 0.47/0.64  cnf(c_0_85, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk4_0,X1,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_51]), c_0_34])])).
% 0.47/0.64  cnf(c_0_86, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_54]), c_0_84])).
% 0.47/0.64  cnf(c_0_87, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_50]), c_0_54])])).
% 0.47/0.64  cnf(c_0_88, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.47/0.64  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_88])]), ['proof']).
% 0.47/0.64  # SZS output end CNFRefutation
% 0.47/0.64  # Proof object total steps             : 90
% 0.47/0.64  # Proof object clause steps            : 54
% 0.47/0.64  # Proof object formula steps           : 36
% 0.47/0.64  # Proof object conjectures             : 33
% 0.47/0.64  # Proof object clause conjectures      : 30
% 0.47/0.64  # Proof object formula conjectures     : 3
% 0.47/0.64  # Proof object initial clauses used    : 25
% 0.47/0.64  # Proof object initial formulas used   : 18
% 0.47/0.64  # Proof object generating inferences   : 23
% 0.47/0.64  # Proof object simplifying inferences  : 42
% 0.47/0.64  # Training examples: 0 positive, 0 negative
% 0.47/0.64  # Parsed axioms                        : 21
% 0.47/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.64  # Initial clauses                      : 34
% 0.47/0.64  # Removed in clause preprocessing      : 1
% 0.47/0.64  # Initial clauses in saturation        : 33
% 0.47/0.64  # Processed clauses                    : 1522
% 0.47/0.64  # ...of these trivial                  : 19
% 0.47/0.64  # ...subsumed                          : 954
% 0.47/0.64  # ...remaining for further processing  : 549
% 0.47/0.64  # Other redundant clauses eliminated   : 1
% 0.47/0.64  # Clauses deleted for lack of memory   : 0
% 0.47/0.64  # Backward-subsumed                    : 35
% 0.47/0.64  # Backward-rewritten                   : 98
% 0.47/0.64  # Generated clauses                    : 13149
% 0.47/0.64  # ...of the previous two non-trivial   : 12301
% 0.47/0.64  # Contextual simplify-reflections      : 16
% 0.47/0.64  # Paramodulations                      : 13148
% 0.47/0.64  # Factorizations                       : 0
% 0.47/0.64  # Equation resolutions                 : 1
% 0.47/0.64  # Propositional unsat checks           : 0
% 0.47/0.64  #    Propositional check models        : 0
% 0.47/0.64  #    Propositional check unsatisfiable : 0
% 0.47/0.64  #    Propositional clauses             : 0
% 0.47/0.64  #    Propositional clauses after purity: 0
% 0.47/0.64  #    Propositional unsat core size     : 0
% 0.47/0.64  #    Propositional preprocessing time  : 0.000
% 0.47/0.64  #    Propositional encoding time       : 0.000
% 0.47/0.64  #    Propositional solver time         : 0.000
% 0.47/0.64  #    Success case prop preproc time    : 0.000
% 0.47/0.64  #    Success case prop encoding time   : 0.000
% 0.47/0.64  #    Success case prop solver time     : 0.000
% 0.47/0.64  # Current number of processed clauses  : 415
% 0.47/0.64  #    Positive orientable unit clauses  : 52
% 0.47/0.64  #    Positive unorientable unit clauses: 0
% 0.47/0.64  #    Negative unit clauses             : 2
% 0.47/0.64  #    Non-unit-clauses                  : 361
% 0.47/0.64  # Current number of unprocessed clauses: 10704
% 0.47/0.64  # ...number of literals in the above   : 52731
% 0.47/0.64  # Current number of archived formulas  : 0
% 0.47/0.64  # Current number of archived clauses   : 134
% 0.47/0.64  # Clause-clause subsumption calls (NU) : 32841
% 0.47/0.64  # Rec. Clause-clause subsumption calls : 14574
% 0.47/0.64  # Non-unit clause-clause subsumptions  : 941
% 0.47/0.64  # Unit Clause-clause subsumption calls : 692
% 0.47/0.64  # Rewrite failures with RHS unbound    : 0
% 0.47/0.64  # BW rewrite match attempts            : 8
% 0.47/0.64  # BW rewrite match successes           : 7
% 0.47/0.64  # Condensation attempts                : 0
% 0.47/0.64  # Condensation successes               : 0
% 0.47/0.64  # Termbank termtop insertions          : 194928
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.265 s
% 0.47/0.64  # System time              : 0.017 s
% 0.47/0.64  # Total time               : 0.282 s
% 0.47/0.64  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
