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
% DateTime   : Thu Dec  3 11:07:12 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 119 expanded)
%              Number of clauses        :   37 (  50 expanded)
%              Number of leaves         :    5 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  268 (1092 expanded)
%              Number of equality atoms :   27 ( 155 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t165_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_relset_1(X1,X2,X4,X3)
           => r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_2)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(t140_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ! [X5] :
              ( ( v1_relat_1(X5)
                & v1_funct_1(X5) )
             => ( ( r1_partfun1(X3,X5)
                  & r1_relset_1(X1,X2,X4,X3) )
               => r1_partfun1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_partfun1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_relset_1(X1,X2,X4,X3)
             => r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t165_funct_2])).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19,X20,X22,X23,X24,X26] :
      ( ( v1_funct_1(esk2_5(X16,X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(esk2_5(X16,X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ r2_hidden(X20,X19)
        | X19 != k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( esk2_5(X16,X17,X18,X19,X20) = X20
        | ~ r2_hidden(X20,X19)
        | X19 != k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v1_partfun1(esk2_5(X16,X17,X18,X19,X20),X16)
        | ~ r2_hidden(X20,X19)
        | X19 != k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( r1_partfun1(X18,esk2_5(X16,X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | X23 != X22
        | ~ v1_partfun1(X23,X16)
        | ~ r1_partfun1(X18,X23)
        | r2_hidden(X22,X19)
        | X19 != k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ r2_hidden(esk3_4(X16,X17,X18,X24),X24)
        | ~ v1_funct_1(X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | X26 != esk3_4(X16,X17,X18,X24)
        | ~ v1_partfun1(X26,X16)
        | ~ r1_partfun1(X18,X26)
        | X24 = k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v1_funct_1(esk4_4(X16,X17,X18,X24))
        | r2_hidden(esk3_4(X16,X17,X18,X24),X24)
        | X24 = k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(esk4_4(X16,X17,X18,X24),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | r2_hidden(esk3_4(X16,X17,X18,X24),X24)
        | X24 = k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( esk4_4(X16,X17,X18,X24) = esk3_4(X16,X17,X18,X24)
        | r2_hidden(esk3_4(X16,X17,X18,X24),X24)
        | X24 = k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v1_partfun1(esk4_4(X16,X17,X18,X24),X16)
        | r2_hidden(esk3_4(X16,X17,X18,X24),X24)
        | X24 = k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( r1_partfun1(X18,esk4_4(X16,X17,X18,X24))
        | r2_hidden(esk3_4(X16,X17,X18,X24),X24)
        | X24 = k5_partfun1(X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_7,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ~ v1_funct_1(X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ v1_funct_1(X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ r1_partfun1(X30,X32)
      | ~ r1_relset_1(X28,X29,X31,X30)
      | r1_partfun1(X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_partfun1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v1_funct_1(esk8_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)
    & ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),k5_partfun1(esk5_0,esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_partfun1(X4,X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ r1_partfun1(X1,X5)
    | ~ r1_relset_1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( r1_partfun1(esk8_0,X1)
    | ~ r1_relset_1(esk5_0,esk6_0,esk8_0,X2)
    | ~ r1_partfun1(X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r1_relset_1(esk5_0,esk6_0,esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_funct_1(esk2_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_partfun1(X3,X1)
    | ~ v1_partfun1(X1,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ r1_tarski(k5_partfun1(X4,X5,X3),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( v1_partfun1(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r1_partfun1(esk8_0,X1)
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( v1_funct_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_partfun1(X1,esk2_5(X2,X3,X1,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X2,X3,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r1_partfun1(esk8_0,X1)
    | ~ v1_partfun1(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    | ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_12]),c_0_13])])).

cnf(c_0_32,plain,
    ( v1_partfun1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_partfun1(esk8_0,esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ r1_partfun1(esk7_0,esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( r1_partfun1(X1,esk2_5(X2,X3,X1,k5_partfun1(X2,X3,X1),X4))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,k5_partfun1(X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,esk6_0,X1,k5_partfun1(esk5_0,esk6_0,X1),X2),X3)
    | ~ r1_partfun1(esk8_0,esk2_5(esk5_0,esk6_0,X1,k5_partfun1(esk5_0,esk6_0,X1),X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    | ~ r2_hidden(X2,k5_partfun1(esk5_0,esk6_0,X1))
    | ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_29]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_partfun1(esk8_0,esk2_5(X1,X2,esk7_0,k5_partfun1(X1,X2,esk7_0),X3))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21])])).

cnf(c_0_37,plain,
    ( esk2_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_5(esk5_0,esk6_0,esk7_0,k5_partfun1(esk5_0,esk6_0,esk7_0),X1),X2)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))
    | ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21]),c_0_19])])).

cnf(c_0_39,plain,
    ( esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4) = X4
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))
    | ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21]),c_0_19])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1),X2)
    | r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1)
    | ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1),k5_partfun1(esk5_0,esk6_0,esk8_0))
    | r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),k5_partfun1(esk5_0,esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t165_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_relset_1(X1,X2,X4,X3)=>r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_2)).
% 0.20/0.47  fof(d7_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(X4=k5_partfun1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>?[X6]:((((v1_funct_1(X6)&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&X6=X5)&v1_partfun1(X6,X1))&r1_partfun1(X3,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 0.20/0.47  fof(t140_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:((v1_relat_1(X5)&v1_funct_1(X5))=>((r1_partfun1(X3,X5)&r1_relset_1(X1,X2,X4,X3))=>r1_partfun1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_partfun1)).
% 0.20/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.47  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.47  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_relset_1(X1,X2,X4,X3)=>r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)))))), inference(assume_negation,[status(cth)],[t165_funct_2])).
% 0.20/0.47  fof(c_0_6, plain, ![X16, X17, X18, X19, X20, X22, X23, X24, X26]:(((((((v1_funct_1(esk2_5(X16,X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(m1_subset_1(esk2_5(X16,X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|~r2_hidden(X20,X19)|X19!=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(esk2_5(X16,X17,X18,X19,X20)=X20|~r2_hidden(X20,X19)|X19!=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(v1_partfun1(esk2_5(X16,X17,X18,X19,X20),X16)|~r2_hidden(X20,X19)|X19!=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(r1_partfun1(X18,esk2_5(X16,X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(~v1_funct_1(X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|X23!=X22|~v1_partfun1(X23,X16)|~r1_partfun1(X18,X23)|r2_hidden(X22,X19)|X19!=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&((~r2_hidden(esk3_4(X16,X17,X18,X24),X24)|(~v1_funct_1(X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|X26!=esk3_4(X16,X17,X18,X24)|~v1_partfun1(X26,X16)|~r1_partfun1(X18,X26))|X24=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(((((v1_funct_1(esk4_4(X16,X17,X18,X24))|r2_hidden(esk3_4(X16,X17,X18,X24),X24)|X24=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(m1_subset_1(esk4_4(X16,X17,X18,X24),k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|r2_hidden(esk3_4(X16,X17,X18,X24),X24)|X24=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(esk4_4(X16,X17,X18,X24)=esk3_4(X16,X17,X18,X24)|r2_hidden(esk3_4(X16,X17,X18,X24),X24)|X24=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(v1_partfun1(esk4_4(X16,X17,X18,X24),X16)|r2_hidden(esk3_4(X16,X17,X18,X24),X24)|X24=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(r1_partfun1(X18,esk4_4(X16,X17,X18,X24))|r2_hidden(esk3_4(X16,X17,X18,X24),X24)|X24=k5_partfun1(X16,X17,X18)|(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).
% 0.20/0.47  fof(c_0_7, plain, ![X28, X29, X30, X31, X32]:(~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|(~v1_funct_1(X31)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|(~v1_relat_1(X32)|~v1_funct_1(X32)|(~r1_partfun1(X30,X32)|~r1_relset_1(X28,X29,X31,X30)|r1_partfun1(X31,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_partfun1])])])).
% 0.20/0.47  fof(c_0_8, negated_conjecture, ((v1_funct_1(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((v1_funct_1(esk8_0)&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r1_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)&~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),k5_partfun1(esk5_0,esk6_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.47  fof(c_0_9, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.47  cnf(c_0_10, plain, (r2_hidden(X4,X6)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X1!=X4|~v1_partfun1(X1,X2)|~r1_partfun1(X5,X1)|X6!=k5_partfun1(X2,X3,X5)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_11, plain, (r1_partfun1(X4,X5)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X5)|~v1_funct_1(X5)|~r1_partfun1(X1,X5)|~r1_relset_1(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.47  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  fof(c_0_14, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.47  cnf(c_0_15, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_17, plain, (r2_hidden(X1,k5_partfun1(X2,X3,X4))|~r1_partfun1(X4,X1)|~v1_partfun1(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).
% 0.20/0.47  cnf(c_0_18, negated_conjecture, (r1_partfun1(esk8_0,X1)|~r1_relset_1(esk5_0,esk6_0,esk8_0,X2)|~r1_partfun1(X2,X1)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.20/0.47  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_20, negated_conjecture, (r1_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  cnf(c_0_23, plain, (m1_subset_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_24, plain, (v1_funct_1(esk2_5(X1,X2,X3,X4,X5))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r1_partfun1(X3,X1)|~v1_partfun1(X1,X4)|~v1_funct_1(X3)|~v1_funct_1(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~r1_tarski(k5_partfun1(X4,X5,X3),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.47  cnf(c_0_26, plain, (v1_partfun1(esk2_5(X1,X2,X3,X4,X5),X1)|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_27, negated_conjecture, (r1_partfun1(esk8_0,X1)|~r1_partfun1(esk7_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.20/0.47  cnf(c_0_28, plain, (v1_relat_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.47  cnf(c_0_29, plain, (v1_funct_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.47  cnf(c_0_30, plain, (r1_partfun1(X1,esk2_5(X2,X3,X1,X4,X5))|~r2_hidden(X5,X4)|X4!=k5_partfun1(X2,X3,X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,X2)|~r1_partfun1(esk8_0,X1)|~v1_partfun1(X1,esk5_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))|~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_12]), c_0_13])])).
% 0.20/0.47  cnf(c_0_32, plain, (v1_partfun1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (r1_partfun1(esk8_0,esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))|~r1_partfun1(esk7_0,esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.20/0.47  cnf(c_0_34, plain, (r1_partfun1(X1,esk2_5(X2,X3,X1,k5_partfun1(X2,X3,X1),X4))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,k5_partfun1(X2,X3,X1))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.47  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_5(esk5_0,esk6_0,X1,k5_partfun1(esk5_0,esk6_0,X1),X2),X3)|~r1_partfun1(esk8_0,esk2_5(esk5_0,esk6_0,X1,k5_partfun1(esk5_0,esk6_0,X1),X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))|~r2_hidden(X2,k5_partfun1(esk5_0,esk6_0,X1))|~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_29]), c_0_32])).
% 0.20/0.47  cnf(c_0_36, negated_conjecture, (r1_partfun1(esk8_0,esk2_5(X1,X2,esk7_0,k5_partfun1(X1,X2,esk7_0),X3))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X3,k5_partfun1(X1,X2,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_21])])).
% 0.20/0.47  cnf(c_0_37, plain, (esk2_5(X1,X2,X3,X4,X5)=X5|~r2_hidden(X5,X4)|X4!=k5_partfun1(X1,X2,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_5(esk5_0,esk6_0,esk7_0,k5_partfun1(esk5_0,esk6_0,esk7_0),X1),X2)|~r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))|~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_21]), c_0_19])])).
% 0.20/0.47  cnf(c_0_39, plain, (esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4)=X4|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r2_hidden(X4,k5_partfun1(X1,X2,X3))), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.47  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))|~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_21]), c_0_19])])).
% 0.20/0.47  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1),X2)|r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1)|~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.47  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1),k5_partfun1(esk5_0,esk6_0,esk8_0))|r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (~r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),k5_partfun1(esk5_0,esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_45]), c_0_46]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 48
% 0.20/0.47  # Proof object clause steps            : 37
% 0.20/0.47  # Proof object formula steps           : 11
% 0.20/0.47  # Proof object conjectures             : 20
% 0.20/0.47  # Proof object clause conjectures      : 17
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 17
% 0.20/0.47  # Proof object initial formulas used   : 5
% 0.20/0.47  # Proof object generating inferences   : 14
% 0.20/0.47  # Proof object simplifying inferences  : 26
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 7
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 26
% 0.20/0.47  # Removed in clause preprocessing      : 0
% 0.20/0.47  # Initial clauses in saturation        : 26
% 0.20/0.47  # Processed clauses                    : 422
% 0.20/0.47  # ...of these trivial                  : 0
% 0.20/0.47  # ...subsumed                          : 116
% 0.20/0.47  # ...remaining for further processing  : 306
% 0.20/0.47  # Other redundant clauses eliminated   : 8
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 32
% 0.20/0.47  # Backward-rewritten                   : 0
% 0.20/0.47  # Generated clauses                    : 1720
% 0.20/0.47  # ...of the previous two non-trivial   : 1669
% 0.20/0.47  # Contextual simplify-reflections      : 62
% 0.20/0.47  # Paramodulations                      : 1713
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 8
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 241
% 0.20/0.47  #    Positive orientable unit clauses  : 8
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 1
% 0.20/0.47  #    Non-unit-clauses                  : 232
% 0.20/0.47  # Current number of unprocessed clauses: 1269
% 0.20/0.47  # ...number of literals in the above   : 8347
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 58
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 19282
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 2427
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 210
% 0.20/0.47  # Unit Clause-clause subsumption calls : 6
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 3
% 0.20/0.47  # BW rewrite match successes           : 0
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 79309
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.111 s
% 0.20/0.47  # System time              : 0.012 s
% 0.20/0.47  # Total time               : 0.122 s
% 0.20/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
