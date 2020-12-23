%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   83 (5241 expanded)
%              Number of clauses        :   59 (1795 expanded)
%              Number of leaves         :   12 (1323 expanded)
%              Depth                    :   21
%              Number of atoms          :  276 (30671 expanded)
%              Number of equality atoms :   93 (4929 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( X2 != k1_xboole_0
          & ? [X4] :
              ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)) )
          & ~ v2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( X2 != k1_xboole_0
            & ? [X4] :
                ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)) )
            & ~ v2_funct_1(X3) ) ) ),
    inference(assume_negation,[status(cth)],[t37_funct_2])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & esk2_0 != k1_xboole_0
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))
    & ~ v2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X33] : k6_partfun1(X33) = k6_relat_1(X33) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ r2_relset_1(X13,X14,X15,X16)
        | X15 = X16
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X15 != X16
        | r2_relset_1(X13,X14,X15,X16)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X17] : m1_subset_1(k6_relat_1(X17),k1_zfmisc_1(k2_zfmisc_1(X17,X17))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_19,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( v1_funct_1(k1_partfun1(X21,X22,X23,X24,X25,X26))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( m1_subset_1(k1_partfun1(X21,X22,X23,X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(X21,X24)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_23,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( ( X36 = k1_xboole_0
        | v2_funct_1(X37)
        | ~ v2_funct_1(k1_partfun1(X34,X35,X35,X36,X37,X38))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X35,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X35 != k1_xboole_0
        | v2_funct_1(X37)
        | ~ v2_funct_1(k1_partfun1(X34,X35,X35,X36,X37,X38))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X35,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_25,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_31,plain,(
    ! [X9] :
      ( v1_relat_1(k6_relat_1(X9))
      & v2_funct_1(k6_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X20 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X20 != k1_xboole_0
        | v1_funct_2(X20,X18,X19)
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_27]),c_0_28]),c_0_36]),c_0_37]),c_0_29]),c_0_30]),c_0_38])]),c_0_39])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_42]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_48,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ~ v1_funct_1(X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ v1_funct_1(X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_partfun1(X27,X28,X29,X30,X31,X32) = k5_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_52,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k1_partfun1(k1_xboole_0,esk2_0,esk2_0,k1_xboole_0,esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_42]),c_0_42]),c_0_42]),c_0_50]),c_0_51])).

cnf(c_0_55,plain,
    ( k1_partfun1(X1,X2,X3,X4,X5,X6) = k1_partfun1(X7,X8,X9,X10,X5,X6)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_51])).

cnf(c_0_57,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_53]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_42]),c_0_53])).

cnf(c_0_59,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_60,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_relset_1(X10,X11,X12) = k1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_61,negated_conjecture,
    ( k1_partfun1(X1,X2,X3,X4,esk3_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_28]),c_0_41]),c_0_57]),c_0_53]),c_0_58])])).

cnf(c_0_62,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_53])).

cnf(c_0_63,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_61]),c_0_56]),c_0_28])])).

cnf(c_0_65,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_53])])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_53]),c_0_57])])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,X1)
    | k1_relat_1(esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_58])).

cnf(c_0_68,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_41]),c_0_58])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,X1)
    | k1_relset_1(X2,X3,esk3_0) != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_30]),c_0_37])]),c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( k1_partfun1(X1,X2,X3,X4,esk3_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_69])])).

cnf(c_0_73,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X2,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_53]),c_0_58])])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,esk2_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_42]),c_0_42])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ v1_funct_2(esk3_0,X3,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_72]),c_0_56]),c_0_28]),c_0_69]),c_0_73])]),c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_53]),c_0_77]),c_0_58])])).

cnf(c_0_80,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relset_1(X2,X1,k1_xboole_0) != X2 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_69]),c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_63]),c_0_69])])])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t37_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2!=k1_xboole_0&?[X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))))&~(v2_funct_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 0.13/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.13/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.38  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.13/0.38  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 0.13/0.38  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.13/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.38  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.13/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~(((X2!=k1_xboole_0&?[X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))))&~(v2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t37_funct_2])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((esk2_0!=k1_xboole_0&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))))&~v2_funct_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X33]:k6_partfun1(X33)=k6_relat_1(X33), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.13/0.38  fof(c_0_15, plain, ![X13, X14, X15, X16]:((~r2_relset_1(X13,X14,X15,X16)|X15=X16|(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))&(X15!=X16|r2_relset_1(X13,X14,X15,X16)|(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_18, plain, ![X17]:m1_subset_1(k6_relat_1(X17),k1_zfmisc_1(k2_zfmisc_1(X17,X17))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.13/0.38  cnf(c_0_19, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_22, plain, ![X21, X22, X23, X24, X25, X26]:((v1_funct_1(k1_partfun1(X21,X22,X23,X24,X25,X26))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~v1_funct_1(X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(m1_subset_1(k1_partfun1(X21,X22,X23,X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(X21,X24)))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|~v1_funct_1(X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.13/0.38  fof(c_0_23, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_24, plain, ![X34, X35, X36, X37, X38]:((X36=k1_xboole_0|v2_funct_1(X37)|~v2_funct_1(k1_partfun1(X34,X35,X35,X36,X37,X38))|(~v1_funct_1(X38)|~v1_funct_2(X38,X35,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))|(~v1_funct_1(X37)|~v1_funct_2(X37,X34,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(X35!=k1_xboole_0|v2_funct_1(X37)|~v2_funct_1(k1_partfun1(X34,X35,X35,X36,X37,X38))|(~v1_funct_1(X38)|~v1_funct_2(X38,X35,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))|(~v1_funct_1(X37)|~v1_funct_2(X37,X34,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_26, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_31, plain, ![X9]:(v1_relat_1(k6_relat_1(X9))&v2_funct_1(k6_relat_1(X9))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.13/0.38  fof(c_0_32, plain, ![X18, X19, X20]:((((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))&((~v1_funct_2(X20,X18,X19)|X20=k1_xboole_0|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X20!=k1_xboole_0|v1_funct_2(X20,X18,X19)|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_34, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_38, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (~v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_40, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_27]), c_0_28]), c_0_36]), c_0_37]), c_0_29]), c_0_30]), c_0_38])]), c_0_39])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_42]), c_0_41])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|~v1_funct_2(esk4_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_36, c_0_42])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_48, plain, ![X27, X28, X29, X30, X31, X32]:(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_partfun1(X27,X28,X29,X30,X31,X32)=k5_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.13/0.38  cnf(c_0_49, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_50, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.13/0.38  cnf(c_0_52, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_53, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (k1_partfun1(k1_xboole_0,esk2_0,esk2_0,k1_xboole_0,esk3_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_42]), c_0_42]), c_0_42]), c_0_50]), c_0_51])).
% 0.13/0.38  cnf(c_0_55, plain, (k1_partfun1(X1,X2,X3,X4,X5,X6)=k1_partfun1(X7,X8,X9,X10,X5,X6)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))), inference(spm,[status(thm)],[c_0_52, c_0_52])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_27, c_0_51])).
% 0.13/0.38  cnf(c_0_57, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_53]), c_0_50])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_42]), c_0_53])).
% 0.13/0.38  cnf(c_0_59, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  fof(c_0_60, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|k1_relset_1(X10,X11,X12)=k1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k1_partfun1(X1,X2,X3,X4,esk3_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_28]), c_0_41]), c_0_57]), c_0_53]), c_0_58])])).
% 0.13/0.38  cnf(c_0_62, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_53])).
% 0.13/0.38  cnf(c_0_63, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_61]), c_0_56]), c_0_28])])).
% 0.13/0.38  cnf(c_0_65, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relat_1(X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_53])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_53]), c_0_57])])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,X1)|k1_relat_1(esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_58])).
% 0.13/0.38  cnf(c_0_68, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_41]), c_0_58])])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,X1)|k1_relset_1(X2,X3,esk3_0)!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_30]), c_0_37])]), c_0_47])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (k1_partfun1(X1,X2,X3,X4,esk3_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_69])])).
% 0.13/0.38  cnf(c_0_73, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_50])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X2,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_53]), c_0_58])])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (k1_relset_1(k1_xboole_0,esk2_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_42]), c_0_42])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,X2,X1)|~v1_funct_2(esk3_0,X3,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_72]), c_0_56]), c_0_28]), c_0_69]), c_0_73])]), c_0_39])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.38  cnf(c_0_78, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_53]), c_0_77]), c_0_58])])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (X1=k1_xboole_0|k1_relset_1(X2,X1,k1_xboole_0)!=X2), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_69]), c_0_79])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (X1=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_63]), c_0_69])])])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_81])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 83
% 0.13/0.38  # Proof object clause steps            : 59
% 0.13/0.38  # Proof object formula steps           : 24
% 0.13/0.38  # Proof object conjectures             : 39
% 0.13/0.38  # Proof object clause conjectures      : 36
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 24
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 22
% 0.13/0.38  # Proof object simplifying inferences  : 76
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 31
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 30
% 0.13/0.38  # Processed clauses                    : 159
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 25
% 0.13/0.38  # ...remaining for further processing  : 132
% 0.13/0.38  # Other redundant clauses eliminated   : 12
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 8
% 0.13/0.38  # Backward-rewritten                   : 80
% 0.13/0.38  # Generated clauses                    : 185
% 0.13/0.38  # ...of the previous two non-trivial   : 180
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 174
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 12
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 6
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 1
% 0.13/0.38  # Current number of unprocessed clauses: 51
% 0.13/0.38  # ...number of literals in the above   : 285
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 119
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 775
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 318
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 32
% 0.13/0.38  # Unit Clause-clause subsumption calls : 37
% 0.13/0.38  # Rewrite failures with RHS unbound    : 3
% 0.13/0.38  # BW rewrite match attempts            : 77
% 0.13/0.38  # BW rewrite match successes           : 75
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6345
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.040 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.043 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
