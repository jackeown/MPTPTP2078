%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1008+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  55 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 207 expanded)
%              Number of equality atoms :   50 (  92 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_7,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))
    & esk2_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk1_0),esk2_0,esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_relset_1(X10,X11,X12) = k1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | k1_relat_1(X17) != k1_tarski(X16)
      | k2_relat_1(X17) = k1_tarski(k1_funct_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

cnf(c_0_11,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_funct_2(X9,X7,X8)
        | X7 = k1_relset_1(X7,X8,X9)
        | X8 = k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X7 != k1_relset_1(X7,X8,X9)
        | v1_funct_2(X9,X7,X8)
        | X8 = k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( ~ v1_funct_2(X9,X7,X8)
        | X7 = k1_relset_1(X7,X8,X9)
        | X7 != k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X7 != k1_relset_1(X7,X8,X9)
        | v1_funct_2(X9,X7,X8)
        | X7 != k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( ~ v1_funct_2(X9,X7,X8)
        | X9 = k1_xboole_0
        | X7 = k1_xboole_0
        | X8 != k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != k1_xboole_0
        | v1_funct_2(X9,X7,X8)
        | X7 = k1_xboole_0
        | X8 != k1_xboole_0
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_14,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k2_relset_1(X13,X14,X15) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_16,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k1_relset_1(k1_tarski(esk1_0),esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk3_0,X1)) = k2_relat_1(esk3_0)
    | k1_tarski(X1) != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_tarski(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk1_0),esk2_0,esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk1_0),esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk3_0,X1)) = k2_relat_1(esk3_0)
    | k1_tarski(X1) != k1_tarski(esk1_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk3_0,esk1_0)) != k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29]),
    [proof]).

%------------------------------------------------------------------------------
