%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 184 expanded)
%              Number of clauses        :   44 (  80 expanded)
%              Number of leaves         :    5 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  285 (1708 expanded)
%              Number of equality atoms :   27 ( 260 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(t165_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_relset_1(X1,X2,X4,X3)
           => r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_partfun1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,plain,(
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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_relset_1(X1,X2,X4,X3)
             => r1_tarski(k5_partfun1(X1,X2,X3),k5_partfun1(X1,X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t165_funct_2])).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
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

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v1_funct_1(esk8_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & r1_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)
    & ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),k5_partfun1(esk5_0,esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( esk2_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( v1_funct_1(esk2_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r1_partfun1(X1,esk2_5(X2,X3,X1,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X2,X3,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( v1_partfun1(esk2_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r1_partfun1(X4,X5)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ r1_partfun1(X1,X5)
    | ~ r1_relset_1(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_21,plain,
    ( esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4) = X4
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_funct_1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r1_partfun1(X1,esk2_5(X2,X3,X1,k5_partfun1(X2,X3,X1),X4))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X4,k5_partfun1(X2,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( v1_partfun1(esk2_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r1_partfun1(esk8_0,X1)
    | ~ r1_relset_1(esk5_0,esk6_0,esk8_0,X2)
    | ~ r1_partfun1(X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r1_relset_1(esk5_0,esk6_0,esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k5_partfun1(X3,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k5_partfun1(X3,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k5_partfun1(X3,X4,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_36,plain,
    ( v1_partfun1(X1,X2)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X4,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( r1_partfun1(esk8_0,X1)
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_30])])).

cnf(c_0_40,plain,
    ( v1_funct_1(esk1_2(k5_partfun1(X1,X2,X3),X4))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_partfun1(X1,esk1_2(k5_partfun1(X2,X3,X1),X4))
    | r1_tarski(k5_partfun1(X2,X3,X1),X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk8_0))
    | ~ r1_partfun1(esk8_0,X1)
    | ~ v1_partfun1(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19])])).

cnf(c_0_43,negated_conjecture,
    ( v1_partfun1(X1,esk5_0)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_30])])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | m1_subset_1(esk1_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r1_partfun1(esk8_0,X1)
    | ~ r1_partfun1(esk7_0,X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1))
    | r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_30])])).

cnf(c_0_47,negated_conjecture,
    ( r1_partfun1(esk7_0,esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1))
    | r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_30])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk8_0))
    | ~ r1_partfun1(esk8_0,X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1)
    | m1_subset_1(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_28]),c_0_30])])).

cnf(c_0_50,negated_conjecture,
    ( r1_partfun1(esk8_0,esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1))
    | r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_46]),c_0_47])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_2(k5_partfun1(esk5_0,esk6_0,esk7_0),X1),k5_partfun1(esk5_0,esk6_0,esk8_0))
    | r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_49]),c_0_46]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk5_0,esk6_0,esk7_0),k5_partfun1(esk5_0,esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
    [proof]).

%------------------------------------------------------------------------------
