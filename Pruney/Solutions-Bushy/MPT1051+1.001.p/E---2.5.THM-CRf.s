%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1051+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 109 expanded)
%              Number of clauses        :   28 (  42 expanded)
%              Number of leaves         :    5 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 525 expanded)
%              Number of equality atoms :   23 ( 133 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t168_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( ! [X5] : X2 != k1_tarski(X5)
              & k5_partfun1(X1,X2,X3) = k5_partfun1(X1,X2,X4) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_2)).

fof(t167_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4))
              & ! [X5] : X2 != k1_tarski(X5) )
           => r1_relset_1(X1,X2,X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_r1_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_relset_1(X1,X2,X3,X4)
      <=> r1_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

fof(reflexivity_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_relset_1(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ( ! [X5] : X2 != k1_tarski(X5)
                & k5_partfun1(X1,X2,X3) = k5_partfun1(X1,X2,X4) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t168_funct_2])).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ v1_funct_1(X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ r1_tarski(k5_partfun1(X16,X17,X18),k5_partfun1(X16,X17,X19))
      | X17 = k1_tarski(esk1_4(X16,X17,X18,X19))
      | r1_relset_1(X16,X17,X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_funct_2])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X25] :
      ( v1_funct_1(esk4_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & v1_funct_1(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & esk3_0 != k1_tarski(X25)
      & k5_partfun1(esk2_0,esk3_0,esk4_0) = k5_partfun1(esk2_0,esk3_0,esk5_0)
      & ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( X3 = k1_tarski(esk1_4(X2,X3,X1,X4))
    | r1_relset_1(X2,X3,X4,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k5_partfun1(X2,X3,X1),k5_partfun1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r1_relset_1(X8,X9,X10,X11)
        | r1_tarski(X10,X11)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( ~ r1_tarski(X10,X11)
        | r1_relset_1(X8,X9,X10,X11)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_relset_1])])])).

cnf(c_0_12,negated_conjecture,
    ( k1_tarski(esk1_4(X1,X2,X3,esk5_0)) = X2
    | r1_relset_1(X1,X2,esk5_0,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X3,X4)
    | ~ r1_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k1_tarski(esk1_4(X1,X2,esk4_0,esk5_0)) = X2
    | r1_relset_1(X1,X2,esk5_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k5_partfun1(X1,X2,esk4_0),k5_partfun1(X1,X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( k5_partfun1(esk2_0,esk3_0,esk4_0) = k5_partfun1(esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( k1_tarski(esk1_4(X1,X2,X3,esk4_0)) = X2
    | r1_relset_1(X1,X2,esk4_0,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_relset_1(esk2_0,esk3_0,esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_relset_1(esk2_0,esk3_0,esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k1_tarski(esk1_4(X1,X2,esk5_0,esk4_0)) = X2
    | r1_relset_1(X1,X2,esk4_0,esk5_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k5_partfun1(X1,X2,esk5_0),k5_partfun1(X1,X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_9])).

fof(c_0_26,plain,(
    ! [X12,X13,X14,X15] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | r2_relset_1(X12,X13,X14,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_relset_1])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_relset_1(esk2_0,esk3_0,esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r1_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_16]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_31,plain,
    ( r2_relset_1(X2,X3,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( esk4_0 = esk5_0
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_relset_1(esk2_0,esk3_0,X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_37,negated_conjecture,
    ( r2_relset_1(esk2_0,esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
