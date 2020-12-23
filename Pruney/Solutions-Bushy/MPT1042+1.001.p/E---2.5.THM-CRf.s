%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:38 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 194 expanded)
%              Number of clauses        :   26 (  79 expanded)
%              Number of leaves         :    3 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 (1506 expanded)
%              Number of equality atoms :   26 ( 210 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(t158_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_3,plain,(
    ! [X10,X11,X12,X13,X14,X16,X17,X18,X20] :
      ( ( v1_funct_1(esk1_5(X10,X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( m1_subset_1(esk1_5(X10,X11,X12,X13,X14),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( esk1_5(X10,X11,X12,X13,X14) = X14
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v1_partfun1(esk1_5(X10,X11,X12,X13,X14),X10)
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( r1_partfun1(X12,esk1_5(X10,X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | X17 != X16
        | ~ v1_partfun1(X17,X10)
        | ~ r1_partfun1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( ~ r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | X20 != esk2_4(X10,X11,X12,X18)
        | ~ v1_partfun1(X20,X10)
        | ~ r1_partfun1(X12,X20)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v1_funct_1(esk3_4(X10,X11,X12,X18))
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( m1_subset_1(esk3_4(X10,X11,X12,X18),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( esk3_4(X10,X11,X12,X18) = esk2_4(X10,X11,X12,X18)
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v1_partfun1(esk3_4(X10,X11,X12,X18),X10)
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( r1_partfun1(X12,esk3_4(X10,X11,X12,X18))
        | r2_hidden(esk2_4(X10,X11,X12,X18),X18)
        | X18 = k5_partfun1(X10,X11,X12)
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
           => ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_2])).

cnf(c_0_5,plain,
    ( v1_funct_1(esk1_5(X1,X2,X3,X4,X5))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0))
    & ( ~ v1_funct_1(esk7_0)
      | ~ v1_funct_2(esk7_0,esk4_0,esk5_0)
      | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( esk1_5(X1,X2,X3,X4,X5) = X5
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( v1_funct_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4) = X4
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1))
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk7_0,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1) = X1
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_10])])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_9]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_1(esk7_0)
    | ~ v1_funct_2(esk7_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_23,plain,
    ( v1_partfun1(esk1_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,X4)
    | X4 != k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ( v1_funct_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_partfun1(X9,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( v1_funct_2(X9,X7,X8)
        | ~ v1_funct_1(X9)
        | ~ v1_partfun1(X9,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk4_0,esk5_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_27,plain,
    ( v1_partfun1(esk1_5(X1,X2,X3,k5_partfun1(X1,X2,X3),X4),X1)
    | ~ r2_hidden(X4,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( v1_partfun1(esk1_5(esk4_0,esk5_0,esk6_0,k5_partfun1(esk4_0,esk5_0,esk6_0),X1),esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_9]),c_0_10])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_partfun1(esk7_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_21])]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_18]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
